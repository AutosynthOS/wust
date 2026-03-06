use crate::ir::function::FunctionIdx;

use super::{VReg, VRegDef};
use super::block::BlockId;

/// An IR instruction in the function's instruction stream.
#[derive(Debug, Clone)]
pub enum IrInst {
    /// Push a value onto a virtual stack.
    StackPush { def: VRegDef },

    /// Pop a value from a virtual stack.
    StackPop { def: VRegDef },

    /// Arithmetic: dst = lhs op rhs
    Alu {
        op: AluOp,
        dst: VReg,
        lhs: VReg,
        rhs: VReg,
    },

    /// Comparison: dst = (lhs op rhs) ? 1 : 0
    Cmp {
        op: CmpOp,
        dst: VReg,
        lhs: VReg,
        rhs: VReg,
    },

    /// Conditional branch — if cond is truthy, goto block_if, else goto block_else.
    BrIf {
        cond: VReg,
        block_if: BlockId,
        block_else: BlockId,
    },

    /// Unconditional branch.
    Branch { target: BlockId },

    /// Function call.
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
