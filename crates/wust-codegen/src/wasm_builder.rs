use std::collections::HashMap;

use autosynth_codegen::builder::FunctionBuilder;
use autosynth_ir::{AluOp, BlockId, CompOp, Operand, VCode};
use autosynth_isa::{PReg, Width};
use autosynth_regalloc::{VInit, VRegId};
use wust_core::FuncMeta;

use crate::conversion::valtype_to_width;

/// Per-block wasm region state.
#[derive(Clone)]
struct WasmBlockState {
    locals: Vec<VRegId>,
    operands: Vec<VRegId>,
    fibre: Vec<VRegId>,
}

/// Wasm-aware function builder.
pub struct WasmFunctionBuilder {
    pub inner: FunctionBuilder,
    /// Current block's region state.
    state: WasmBlockState,
    /// Snapshots from predecessors, keyed by target block.
    /// Each target accumulates one snapshot per predecessor.
    snapshots: HashMap<BlockId, Vec<WasmBlockState>>,
}

impl WasmFunctionBuilder {
    pub fn new(func: &FuncMeta) -> Self {
        let mut inner = FunctionBuilder::new();

        let mut locals = Vec::new();

        for (i, param) in func.params.iter().enumerate() {
            let w = valtype_to_width(param);
            let vreg = inner.regalloc.define(VInit::PReg(PReg(i as u8)), w);
            locals.push(vreg);
        }

        for local in func.locals.iter() {
            let w = valtype_to_width(local);
            let vreg = inner.regalloc.define(VInit::Const(0), w);
            locals.push(vreg);
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
        let vreg = self.inner.regalloc.define(VInit::Const(val), width);
        self.state.operands.push(vreg);
    }

    pub fn push_local(&mut self, idx: usize) {
        self.state.operands.push(self.state.locals[idx]);
    }

    pub fn pop(&mut self) -> VRegId {
        self.state.operands.pop().expect("operand stack underflow")
    }

    pub fn push(&mut self, vreg: VRegId) {
        self.state.operands.push(vreg);
    }

    pub fn local_set(&mut self, idx: usize, val: VRegId) {
        self.state.locals[idx] = val;
    }

    // --- VCode emission ---

    pub fn binop(&mut self, op: AluOp, width: Width) {
        let rhs = self.pop();
        let lhs = self.pop();
        let dst = self.inner.regalloc.define(VInit::InstDst, width);

        self.inner.push_operand(Operand::VReg(lhs));
        self.inner.push_operand(Operand::VReg(rhs));
        self.inner.push_operand(Operand::VReg(dst));
        self.inner.emit(VCode::Alu { op });

        self.state.operands.push(dst);
    }

    pub fn eqz(&mut self) {
        let val = self.pop();
        let zero = self.inner.regalloc.define(VInit::Const(0), Width::W32);
        let dst = self.inner.regalloc.define(VInit::InstDst, Width::W32);

        self.inner.push_operand(Operand::VReg(val));
        self.inner.push_operand(Operand::VReg(zero));
        self.inner.push_operand(Operand::VReg(dst));
        self.inner.emit(VCode::Alu { op: AluOp::Comp(CompOp::Eq) });

        self.state.operands.push(dst);
    }

    // --- Control flow ---

    /// Emit conditional branch. Snapshots current state for both targets.
    pub fn br_if(&mut self, cond: VRegId, then_block: BlockId, else_block: BlockId) {
        self.inner.push_operand(Operand::VReg(cond));
        self.inner.emit(VCode::BrIf {
            block_if: then_block,
            block_else: else_block,
        });

        self.snapshot_onto(then_block);
        self.snapshot_onto(else_block);
    }

    /// Emit unconditional branch. Snapshots current state for the target.
    pub fn br(&mut self, target: BlockId) {
        self.inner.emit(VCode::Branch { target });
        self.snapshot_onto(target);
    }

    /// Switch to a new block. Restores region state from predecessor
    /// snapshots. At merge points, creates phi VRegs where predecessors
    /// disagree.
    pub fn start_block(&mut self, id: BlockId) {
        self.inner.start_block(id);

        if let Some(snaps) = self.snapshots.remove(&id) {
            if let Some(first) = snaps.first() {
                self.state = first.clone();

                // Merge: create phi VRegs where predecessors differ.
                if snaps.len() > 1 {
                    self.merge_snapshots(&snaps);
                }
            }
        }
    }

    pub fn emit_return(&mut self, func: &FuncMeta) {
        for (i, _) in func.results.iter().enumerate() {
            let result = self.pop();
            self.inner.regalloc.set_target(result, PReg(i as u8));
        }
        self.inner.emit(VCode::Return);
    }

    pub fn build(self) -> autosynth_codegen::ir::IrFunction {
        self.inner.build()
    }

    // --- Internal ---

    /// Save current region state as a snapshot for the target block.
    fn snapshot_onto(&mut self, target: BlockId) {
        self.snapshots
            .entry(target)
            .or_default()
            .push(self.state.clone());
    }

    /// At a merge point, compare snapshots and create phi VRegs
    /// for slots where predecessors disagree.
    fn merge_snapshots(&mut self, snaps: &[WasmBlockState]) {
        // Merge operand stacks.
        for i in 0..self.state.operands.len() {
            let first = self.state.operands[i];
            let all_same = snaps.iter().all(|s| s.operands.get(i) == Some(&first));
            if !all_same {
                // Create a phi VReg — for now just use the first predecessor's value.
                // TODO: proper phi with Move instructions from each predecessor.
                let width = self.inner.regalloc.width(first);
                let phi = self.inner.regalloc.define(VInit::InstDst, width);
                self.state.operands[i] = phi;
            }
        }

        // Merge locals.
        for i in 0..self.state.locals.len() {
            let first = self.state.locals[i];
            let all_same = snaps.iter().all(|s| s.locals.get(i) == Some(&first));
            if !all_same {
                let width = self.inner.regalloc.width(first);
                let phi = self.inner.regalloc.define(VInit::InstDst, width);
                self.state.locals[i] = phi;
            }
        }
    }
}
