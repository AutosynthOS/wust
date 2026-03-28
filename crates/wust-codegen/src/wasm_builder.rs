use autosynth_codegen::builder::FunctionBuilder;
use autosynth_ir::{AluOp, BlockId, Operand, VCode};
use autosynth_isa::{PReg, Width};
use autosynth_regalloc::{VInit, VRegId};
use wust_core::FuncMeta;

use crate::conversion::valtype_to_width;

/// Wasm-aware function builder.
///
/// Wraps [`FunctionBuilder`] and manages wasm-specific state:
/// locals (params + declared locals) and the operand stack.
pub struct WasmFunctionBuilder {
    pub inner: FunctionBuilder,
    locals: Vec<VRegId>,
    operands: Vec<VRegId>,
}

impl WasmFunctionBuilder {
    /// Create a new builder from a wasm function signature.
    ///
    /// Automatically sets up params (each in its CC register x0..xN)
    /// and zero-initialized locals. Starts in the Entry block.
    pub fn new(func: &FuncMeta) -> Self {
        let mut inner = FunctionBuilder::new();
        inner.start_block(BlockId::Entry);

        let mut locals = Vec::new();

        // Params — each arrives in a CC register.
        for (i, param) in func.params.iter().enumerate() {
            let w = valtype_to_width(param);
            let vreg = inner.regalloc.define(VInit::PReg(PReg(i as u8)), w);
            locals.push(vreg);
        }

        // Declared locals — zero-initialized.
        for local in func.locals.iter() {
            let w = valtype_to_width(local);
            let vreg = inner.regalloc.define(VInit::Const(0), w);
            locals.push(vreg);
        }

        Self {
            inner,
            locals,
            operands: Vec::new(),
        }
    }

    /// Push a constant onto the wasm operand stack.
    pub fn push_const(&mut self, val: i64, width: Width) {
        let vreg = self.inner.regalloc.define(VInit::Const(val), width);
        self.operands.push(vreg);
    }

    /// Push a local's VReg onto the wasm operand stack.
    pub fn push_local(&mut self, idx: usize) {
        self.operands.push(self.locals[idx]);
    }

    /// Pop from the wasm operand stack.
    pub fn pop(&mut self) -> VRegId {
        self.operands.pop().expect("operand stack underflow")
    }

    /// Push a VReg onto the wasm operand stack.
    pub fn push(&mut self, vreg: VRegId) {
        self.operands.push(vreg);
    }

    /// Set a local slot to a VReg.
    pub fn local_set(&mut self, idx: usize, val: VRegId) {
        self.locals[idx] = val;
    }

    /// Emit a binary ALU op: pop two, push result.
    pub fn binop(&mut self, op: AluOp, width: Width) {
        let rhs = self.pop();
        let lhs = self.pop();
        let dst = self.inner.regalloc.define(VInit::InstDst, width);

        self.inner.push_operand(Operand::VReg(lhs));
        self.inner.push_operand(Operand::VReg(rhs));
        self.inner.push_operand(Operand::VReg(dst));
        self.inner.emit(VCode::Alu { op });

        self.operands.push(dst);
    }

    /// Emit a return instruction.
    pub fn emit_return(&mut self) {
        self.inner.emit(VCode::Return);
    }

    /// Build and return the completed IR function.
    pub fn build(self) -> autosynth_codegen::builder::IrFunction {
        self.inner.build()
    }
}
