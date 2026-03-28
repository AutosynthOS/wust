use std::collections::BTreeMap;

use autosynth_codegen::builder::{FunctionBuilder, VRefSource, VRegOrRef};
use autosynth_ir::{AluOp, BlockId, CompOp, Operand, VCode, VReg};
use autosynth_isa::{PReg, Width};
use autosynth_regalloc::VInit;
use wust_core::FuncMeta;

use crate::conversion::valtype_to_width;
use crate::wasm_block::WasmBlock;

/// Wasm-aware function builder.
pub struct WasmFunctionBuilder {
    pub inner: FunctionBuilder,
    blocks: BTreeMap<BlockId, WasmBlock>,
}

impl WasmFunctionBuilder {
    pub fn new(func: &FuncMeta) -> Self {
        let mut inner = FunctionBuilder::new();

        let mut locals = Vec::new();
        for (i, param) in func.params.iter().enumerate() {
            let id = inner.regalloc.define(VInit::PReg(PReg(i as u8)), valtype_to_width(param));
            locals.push(VRegOrRef::VReg(id));
        }
        for local in func.locals.iter() {
            let id = inner.regalloc.define(VInit::Const(0), valtype_to_width(local));
            locals.push(VRegOrRef::VReg(id));
        }

        let entry_block = WasmBlock {
            regions: BTreeMap::from([
                ("locals", locals),
                ("operands", Vec::new()),
                ("fibre", Vec::new()),
            ]),
        };

        let mut blocks = BTreeMap::new();
        blocks.insert(BlockId::Entry, entry_block);

        Self { inner, blocks }
    }

    fn current_id(&self) -> BlockId {
        self.inner.current_block_id()
    }

    fn current(&mut self) -> &mut WasmBlock {
        let id = self.current_id();
        self.blocks.get_mut(&id).expect("no current wasm block")
    }

    // --- Region operations ---

    pub fn push_const(&mut self, val: i64, width: Width) {
        let id = self.inner.regalloc.define(VInit::Const(val), width);
        self.current().region("operands").push(VRegOrRef::VReg(id));
    }

    pub fn push_local(&mut self, idx: usize) {
        let val = self.current().region_ref("locals")[idx];
        self.current().region("operands").push(val);
    }

    pub fn pop(&mut self) -> VRegOrRef {
        self.current().region("operands").pop().expect("operand stack underflow")
    }

    pub fn push(&mut self, val: VRegOrRef) {
        self.current().region("operands").push(val);
    }

    pub fn local_set(&mut self, idx: usize, val: VRegOrRef) {
        self.current().region("locals")[idx] = val;
    }

    // --- VCode emission ---

    /// Resolve a VRegOrRef to a VReg for operand emission.
    /// Direct refs chase to source. Phi refs create a new VRegDef.
    fn resolve_to_vreg(&mut self, val: VRegOrRef) -> VReg {
        match val {
            VRegOrRef::VReg(vreg) => vreg,
            VRegOrRef::Ref(ref_id) => {
                match self.inner.ref_source(ref_id).clone() {
                    VRefSource::Direct(inner) => self.resolve_to_vreg(inner),
                    VRefSource::Phi(sources) => {
                        let resolved: Vec<VReg> = sources.into_iter()
                            .map(|s| self.resolve_to_vreg(s))
                            .collect();
                        let width = self.inner.regalloc.width(resolved[0]);
                        self.inner.regalloc.define(VInit::Phi(resolved), width)
                    }
                }
            }
        }
    }

    pub fn binop(&mut self, op: AluOp, width: Width) {
        let rhs = self.pop();
        let lhs = self.pop();
        let rhs = self.resolve_to_vreg(rhs);
        let lhs = self.resolve_to_vreg(lhs);
        let dst = self.inner.regalloc.define(VInit::InstDst, width);

        self.inner.push_operand(lhs);
        self.inner.push_operand(rhs);
        self.inner.push_operand(dst);
        self.inner.emit(VCode::Alu { op });

        self.current().region("operands").push(VRegOrRef::VReg(dst));
    }

    pub fn eqz(&mut self) {
        let val = self.pop();
        let val = self.resolve_to_vreg(val);
        let zero = self.inner.regalloc.define(VInit::Const(0), Width::W32);
        let dst = self.inner.regalloc.define(VInit::InstDst, Width::W32);

        self.inner.push_operand(VRegOrRef::VReg(val));
        self.inner.push_operand(VRegOrRef::VReg(zero));
        self.inner.push_operand(VRegOrRef::VReg(dst));
        self.inner.emit(VCode::Alu { op: AluOp::Comp(CompOp::Eq) });

        self.current().region("operands").push(VRegOrRef::VReg(dst));
    }

    // --- Control flow ---

    pub fn br_if(&mut self, cond: VRegOrRef, then_block: BlockId, else_block: BlockId) {
        let fused = match self.inner.current_block().vcode.back() {
            Some(VCode::Alu { op: AluOp::Comp(comp_op) }) => Some(*comp_op),
            _ => None,
        };

        if let Some(comp_op) = fused {
            let block = self.inner.current_block_mut();
            block.vcode.pop_back();
            block.operands.pop(); // dst
            if let (Some(rhs), Some(lhs)) = (block.operands.pop(), block.operands.pop()) {
                self.inner.push_operand(lhs);
                self.inner.push_operand(rhs);
            }
            self.inner.emit(VCode::BrIf {
                op: comp_op,
                block_if: then_block,
                block_else: else_block,
            });
        } else {
            let cond = self.resolve_to_vreg(cond);
            let zero = self.inner.regalloc.define(VInit::Const(0), Width::W32);
            self.inner.push_operand(cond);
            self.inner.push_operand(zero);
            self.inner.emit(VCode::BrIf {
                op: CompOp::Ne,
                block_if: then_block,
                block_else: else_block,
            });
        }

        // Fork current block state to both successors.
        let fork = self.current().fork();
        self.ensure_or_merge(then_block, &fork);
        self.ensure_or_merge(else_block, &fork);
    }

    pub fn br(&mut self, target: BlockId) {
        self.inner.emit(VCode::Branch { target });

        let fork = self.current().fork();
        self.ensure_or_merge(target, &fork);
    }

    pub fn start_block(&mut self, id: BlockId) {
        self.inner.start_block(id);
        // Block should already exist from a predecessor's br/br_if.
    }

    pub fn emit_return(&mut self, func: &FuncMeta) {
        for (i, _) in func.results.iter().enumerate() {
            let result = self.pop();
            let vreg = self.resolve_to_vreg(result);
            self.inner.regalloc.set_target(vreg, PReg(i as u8));
        }
        self.inner.emit(VCode::Return);
    }

    pub fn build(self) -> autosynth_codegen::ir::IrFunction {
        self.inner.build()
    }

    // --- Internal ---

    /// If the target block doesn't exist, create it from the fork.
    /// If it already exists (another predecessor got there first), merge.
    fn ensure_or_merge(&mut self, target: BlockId, fork: &WasmBlock) {
        if let Some(existing) = self.blocks.get_mut(&target) {
            existing.merge(fork, &mut self.inner);
        } else {
            self.blocks.insert(target, fork.clone());
        }
    }
}
