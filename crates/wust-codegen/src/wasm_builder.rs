use autosynth_codegen::builder::FunctionBuilder;
use autosynth_ir::{AluOp, BlockId, CompOp, Operand, VCode};
use autosynth_isa::{PReg, Width};
use autosynth_regalloc::{VInit, VRegId};

/// Wasm-aware function builder.
///
/// Wraps [`FunctionBuilder`] and manages wasm-specific regions
/// (locals, operands, fibre). Emits VCode + operands to the
/// underlying builder.
pub struct WasmFunctionBuilder {
    pub inner: FunctionBuilder,
    /// Wasm local variables — each slot holds a VRegId.
    locals: Vec<VRegId>,
    /// Wasm operand stack.
    operands: Vec<VRegId>,
}

impl WasmFunctionBuilder {
    pub fn new() -> Self {
        Self {
            inner: FunctionBuilder::new(),
            locals: Vec::new(),
            operands: Vec::new(),
        }
    }

    /// Declare a function parameter. Defines a VReg with PReg origin
    /// (arrives in CC register) and pushes to locals.
    pub fn declare_param(&mut self, idx: usize, width: Width) {
        let vreg = self.inner.regalloc.define(VInit::PReg(PReg(idx as u8)), width);
        self.locals.push(vreg);
    }

    /// Declare a zero-initialized local.
    pub fn declare_local(&mut self, width: Width) {
        let vreg = self.inner.regalloc.define(VInit::Const(0), width);
        self.locals.push(vreg);
    }

    /// Push a constant onto the wasm operand stack.
    pub fn push_const(&mut self, val: i64, width: Width) {
        let vreg = self.inner.regalloc.define(VInit::Const(val), width);
        self.operands.push(vreg);
    }

    /// Push a local's VReg onto the wasm operand stack.
    pub fn push_local(&mut self, idx: usize) {
        let vreg = self.locals[idx];
        self.operands.push(vreg);
    }

    /// Pop from the wasm operand stack.
    pub fn pop(&mut self) -> VRegId {
        self.operands.pop().expect("operand stack underflow")
    }

    /// Push a VReg onto the wasm operand stack.
    pub fn push(&mut self, vreg: VRegId) {
        self.operands.push(vreg);
    }

    /// Emit a binary ALU op: pop two, push result.
    pub fn binop(&mut self, op: AluOp, width: Width) {
        let rhs = self.pop();
        let lhs = self.pop();
        let dst = self.inner.regalloc.define(VInit::InstDst, width);

        let lhs_width = self.inner.regalloc.width(lhs);
        let rhs_width = self.inner.regalloc.width(rhs);

        self.inner.push_operand(Operand::VReg { id: lhs, width: lhs_width });
        self.inner.push_operand(Operand::VReg { id: rhs, width: rhs_width });
        self.inner.push_operand(Operand::VReg { id: dst, width });
        self.inner.emit(VCode::Alu { op });

        self.operands.push(dst);
    }

    /// Emit a return. Pops the result from the operand stack and
    /// emits a Return VCode instruction.
    pub fn emit_return(&mut self) {
        // Result is on top of operand stack — the regalloc/emitter
        // will ensure it ends up in x0.
        self.inner.emit(VCode::Return);
    }

    /// Start a new block.
    pub fn start_block(&mut self, id: BlockId) {
        self.inner.start_block(id);
    }

    /// Build and return the completed IR function.
    pub fn build(self) -> autosynth_codegen::builder::IrFunction {
        self.inner.build()
    }
}
