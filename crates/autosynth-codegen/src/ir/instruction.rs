use crate::ir::function::FunctionIdx;

use super::{Register, VReg, VRegDef};
use super::block::BlockId;

/// An IR instruction in the function's instruction stream.
#[derive(Debug, Clone)]
pub enum IrInst {
    /// Push a value onto a virtual stack.
    StackPush { def: VRegDef },

    /// Pop a value from a virtual stack.
    StackPop { def: VRegDef },

    /// Arithmetic: dst = lhs op rhs.
    ///
    /// Operands can be virtual or physical registers. The lowerer
    /// checks VRegDef values to fold constants into immediates.
    Alu {
        op: AluOp,
        dst: Register,
        lhs: Register,
        rhs: Register,
    },

    /// Comparison: sets flags from (lhs op rhs). The dst register is a
    /// placeholder — the result lives in CPU flags, consumed by BrIf.
    Cmp {
        op: CmpOp,
        dst: Register,
        lhs: Register,
        rhs: Register,
    },

    /// Conditional branch — if cond is truthy, goto block_if, else goto block_else.
    BrIf {
        cond: VReg,
        block_if: BlockId,
        block_else: BlockId,
    },

    /// Unconditional branch.
    Branch { target: BlockId },

    /// Function call (branch-and-link to another function).
    ///
    /// The lowerer flushes dirty registers before and invalidates after.
    Call {
        func_idx: FunctionIdx,
    },

    /// Return from function.
    Return { values: Vec<VReg> },
}

/// Arithmetic operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AluOp {
    Add,
    Sub,
    Mul,
    And,
    Or,
    Xor,
    Shl,
    ShrS,
    ShrU,
}

/// Comparison operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CmpOp {
    Eq,
    Ne,
    LtS,
    LtU,
    GtS,
    GtU,
    LeS,
    LeU,
    GeS,
    GeU,
}
