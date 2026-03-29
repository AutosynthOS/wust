use std::collections::BTreeMap;

use autosynth_codegen::builder::{BuilderItem, FunctionBuilder, VRegOrRef};
use autosynth_ir::{AluOp, BlockId, CompOp, Operand, VCode, VReg};
use autosynth_isa::{PReg, Width};
use autosynth_regalloc::{MachineConfig, VInit};
use wust_core::FuncMeta;

use crate::conversion::valtype_to_width;
use crate::wasm_block::WasmBlock;

/// Wasm-aware function builder.
pub struct WasmFunctionBuilder {
    pub inner: FunctionBuilder,
    blocks: BTreeMap<BlockId, WasmBlock>,
}

impl WasmFunctionBuilder {
    pub fn new(func: &FuncMeta, config: MachineConfig) -> Self {
        let mut inner = FunctionBuilder::new(config);

        let mut locals = Vec::new();
        for (i, param) in func.params.iter().enumerate() {
            let id = inner.define(VInit::PReg(PReg(i as u8)), valtype_to_width(param));
            locals.push(VRegOrRef::VReg(id));
        }
        for local in func.locals.iter() {
            let id = inner.define(VInit::Const(0), valtype_to_width(local));
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

    fn region(&mut self, name: &str) -> &mut Vec<VRegOrRef> {
        self.current().region(name)
    }

    fn region_ref(&self, name: &str) -> &[VRegOrRef] {
        let id = self.inner.current_block_id();
        self.blocks[&id].region_ref(name)
    }

    // --- Region operations ---

    pub fn push_const(&mut self, val: i64, width: Width) {
        let id = self.inner.define(VInit::Const(val), width);
        self.region("operands").push(VRegOrRef::VReg(id));
    }

    pub fn push_local(&mut self, idx: usize) {
        let local = self.region_ref("locals")[idx];
        let source = self.inner.resolve(local);
        let width = self.inner.width(source);
        let copy = self.inner.define(VInit::Copy(source), width);
        self.region("operands").push(VRegOrRef::VReg(copy));
    }

    pub fn pop(&mut self) -> VRegOrRef {
        self.region("operands").pop().expect("operand stack underflow")
    }

    pub fn push(&mut self, val: VRegOrRef) {
        self.region("operands").push(val);
    }

    pub fn local_set(&mut self, idx: usize, val: VRegOrRef) {
        self.region("locals")[idx] = val;
    }

    // --- VCode emission ---

    pub fn binop(&mut self, op: AluOp, width: Width) {
        let rhs = self.pop();
        let lhs = self.pop();
        let dst = self.inner.define(VInit::InstDst, width);

        self.inner.push_operand(lhs);
        self.inner.push_operand(rhs);
        self.inner.emit(VCode::Alu { op });
        self.inner.emit(VCode::Operand(Operand::DstVReg(dst)));

        self.region("operands").push(VRegOrRef::VReg(dst));
    }

    pub fn eqz(&mut self) {
        let val = self.pop();
        let zero = self.inner.define(VInit::Const(0), Width::W32);
        let dst = self.inner.define(VInit::InstDst, Width::W32);

        self.inner.push_operand(val);
        self.inner.push_operand(zero);
        self.inner.emit(VCode::Alu { op: AluOp::Comp(CompOp::Eq) });
        self.inner.emit(VCode::Operand(Operand::DstVReg(dst)));

        self.region("operands").push(VRegOrRef::VReg(dst));
    }

    // --- Control flow ---

    pub fn br_if(&mut self, cond: VRegOrRef, then_block: BlockId, else_block: BlockId) {
        // No fusion — just emit BrIf(Ne, cond, 0).
        // A fuser pass can optimize this later.
        let zero = self.inner.define(VInit::Const(0), Width::W32);
        self.inner.push_operand(cond);
        self.inner.push_operand(zero);
        self.inner.emit(VCode::BrIf {
            op: CompOp::Ne,
            block_if: then_block,
            block_else: else_block,
        });

        // Fork current block state to each successor independently.
        let id = self.current_id();
        self.ensure_or_merge(then_block, id);
        self.ensure_or_merge(else_block, id);
    }

    pub fn br(&mut self, target: BlockId) {
        self.inner.emit(VCode::Branch { target });

        let id = self.current_id();
        self.ensure_or_merge(target, id);
    }

    pub fn start_block(&mut self, id: BlockId) {
        self.inner.start_block(id);
        // Block should already exist from a predecessor's br/br_if.
    }

    pub fn emit_return(&mut self, func: &FuncMeta) {
        for (i, _) in func.results.iter().enumerate() {
            let result = self.pop();
            self.inner.set_target(result, PReg(i as u8));
        }
        self.inner.emit(VCode::Return);
    }

    pub fn build(self) -> autosynth_codegen::ir::IrFunction {
        self.inner.build()
    }

    // --- Internal ---

    /// If the target block doesn't exist, fork the source into it
    /// (wrapping all values in Direct refs). If it already exists
    /// (another predecessor got there first), merge the source's
    /// values into the existing refs.
    fn ensure_or_merge(&mut self, target: BlockId, source: BlockId) {
        let src = &self.blocks[&source];
        if self.blocks.contains_key(&target) {
            let src_clone = src.clone();
            let existing = self.blocks.get_mut(&target).unwrap();
            existing.merge(&src_clone, source, &mut self.inner);
        } else {
            let forked = src.fork(source, &mut self.inner);
            self.blocks.insert(target, forked);
        }
    }
}
