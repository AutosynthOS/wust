use std::collections::HashMap;

use autosynth_codegen::builder::FunctionBuilder;
use autosynth_ir::{AluOp, BlockId, CompOp, Operand, VCode, VReg};
use autosynth_isa::{PReg, Width};
use autosynth_regalloc::{VInit, VRegDefId, VRegRefDef};
use wust_core::FuncMeta;

use crate::conversion::valtype_to_width;

/// Per-block wasm region state.
#[derive(Clone)]
struct WasmBlockState {
    locals: Vec<VReg>,
    operands: Vec<VReg>,
    fibre: Vec<VReg>,
}

/// Wasm-aware function builder.
pub struct WasmFunctionBuilder {
    pub inner: FunctionBuilder,
    state: WasmBlockState,
    snapshots: HashMap<BlockId, Vec<WasmBlockState>>,
}

impl WasmFunctionBuilder {
    pub fn new(func: &FuncMeta) -> Self {
        let mut inner = FunctionBuilder::new();

        let mut locals = Vec::new();

        for (i, param) in func.params.iter().enumerate() {
            let w = valtype_to_width(param);
            let id = inner.regalloc.define(VInit::PReg(PReg(i as u8)), w);
            locals.push(VReg::Def(id));
        }

        for local in func.locals.iter() {
            let w = valtype_to_width(local);
            let id = inner.regalloc.define(VInit::Const(0), w);
            locals.push(VReg::Def(id));
        }

        Self {
            inner,
            state: WasmBlockState {
                locals,
                operands: Vec::new(),
                fibre: Vec::new(),
            },
            snapshots: HashMap::new(),
        }
    }

    // --- Region operations ---

    pub fn push_const(&mut self, val: i64, width: Width) {
        let id = self.inner.regalloc.define(VInit::Const(val), width);
        self.state.operands.push(VReg::Def(id));
    }

    pub fn push_local(&mut self, idx: usize) {
        self.state.operands.push(self.state.locals[idx]);
    }

    pub fn pop(&mut self) -> VReg {
        self.state.operands.pop().expect("operand stack underflow")
    }

    pub fn push(&mut self, vreg: VReg) {
        self.state.operands.push(vreg);
    }

    pub fn local_set(&mut self, idx: usize, val: VReg) {
        self.state.locals[idx] = val;
    }

    // --- VCode emission ---

    pub fn binop(&mut self, op: AluOp, width: Width) {
        let rhs = self.pop();
        let lhs = self.pop();
        let dst = self.inner.regalloc.define(VInit::InstDst, width);

        self.inner.push_operand(Operand::VReg(lhs));
        self.inner.push_operand(Operand::VReg(rhs));
        self.inner.push_operand(Operand::VReg(VReg::Def(dst)));
        self.inner.emit(VCode::Alu { op });

        self.state.operands.push(VReg::Def(dst));
    }

    pub fn eqz(&mut self) {
        let val = self.pop();
        let zero = self.inner.regalloc.define(VInit::Const(0), Width::W32);
        let dst = self.inner.regalloc.define(VInit::InstDst, Width::W32);

        self.inner.push_operand(Operand::VReg(val));
        self.inner.push_operand(Operand::VReg(VReg::Def(zero)));
        self.inner.push_operand(Operand::VReg(VReg::Def(dst)));
        self.inner.emit(VCode::Alu {
            op: AluOp::Comp(CompOp::Eq),
        });

        self.state.operands.push(VReg::Def(dst));
    }

    // --- Control flow ---

    pub fn br_if(&mut self, cond: VReg, then_block: BlockId, else_block: BlockId) {
        let fused = match self.inner.current_block().vcode.back() {
            Some(VCode::Alu {
                op: AluOp::Comp(comp_op),
            }) => Some(*comp_op),
            _ => None,
        };

        if let Some(comp_op) = fused {
            let block = self.inner.current_block_mut();
            block.vcode.pop_back();
            block.operands.pop(); // dst
            let rhs = block.operands.pop();
            let lhs = block.operands.pop();
            if let (Some(lhs), Some(rhs)) = (lhs, rhs) {
                self.inner.push_operand(lhs);
                self.inner.push_operand(rhs);
            }
            self.inner.emit(VCode::BrIf {
                op: comp_op,
                block_if: then_block,
                block_else: else_block,
            });
        } else {
            let zero = self.inner.regalloc.define(VInit::Const(0), Width::W32);
            self.inner.push_operand(Operand::VReg(cond));
            self.inner.push_operand(Operand::VReg(VReg::Def(zero)));
            self.inner.emit(VCode::BrIf {
                op: CompOp::Ne,
                block_if: then_block,
                block_else: else_block,
            });
        }

        self.snapshot_onto(then_block);
        self.snapshot_onto(else_block);
    }

    pub fn br(&mut self, target: BlockId) {
        self.inner.emit(VCode::Branch { target });
        self.snapshot_onto(target);
    }

    pub fn start_block(&mut self, id: BlockId) {
        self.inner.start_block(id);

        if let Some(snaps) = self.snapshots.remove(&id) {
            if let Some(first) = snaps.first() {
                // Start with first predecessor's state.
                self.state = first.clone();

                // Wrap all inherited slots in refs.
                self.wrap_in_refs(&snaps);
            }
        }
    }

    pub fn emit_return(&mut self, func: &FuncMeta) {
        for (i, _) in func.results.iter().enumerate() {
            let result = self.pop();
            match result {
                VReg::Def(id) => self.inner.regalloc.set_target(id, PReg(i as u8)),
                VReg::Ref(_) => {
                    // TODO: resolve ref to def and set target
                    todo!("set_target on ref")
                }
            }
        }
        self.inner.emit(VCode::Return);
    }

    pub fn build(self) -> autosynth_codegen::ir::IrFunction {
        self.inner.build()
    }

    // --- Internal ---

    fn snapshot_onto(&mut self, target: BlockId) {
        self.snapshots
            .entry(target)
            .or_default()
            .push(self.state.clone());
    }

    fn wrap_in_refs(&mut self, snaps: &[WasmBlockState]) {
        wrap_slots(
            &mut self.state.operands,
            snaps.iter().map(|s| &s.operands),
            &mut self.inner.regalloc,
        );
        wrap_slots(
            &mut self.state.locals,
            snaps.iter().map(|s| &s.locals),
            &mut self.inner.regalloc,
        );
        wrap_slots(
            &mut self.state.fibre,
            snaps.iter().map(|s| &s.fibre),
            &mut self.inner.regalloc,
        );
    }
}

fn wrap_slots<'a>(
    slots: &mut [VReg],
    snap_regions: impl Iterator<Item = &'a Vec<VReg>> + Clone,
    regalloc: &mut autosynth_regalloc::RegAlloc,
) {
    for i in 0..slots.len() {
        let first = slots[i];
        let all_same = snap_regions.clone().all(|r| r.get(i) == Some(&first));
        let ref_def = if all_same {
            VRegRefDef::Direct(first)
        } else {
            VRegRefDef::Phi(snap_regions.clone().map(|r| r[i]).collect())
        };
        slots[i] = VReg::Ref(regalloc.alloc_ref(ref_def));
    }
}
