//! IR instruction types and operator enums.

use std::fmt;

use crate::ir::function::FunctionIdx;

use super::{Register, VReg, VRegDef};
use super::block::BlockId;

/// An IR instruction in the function's instruction stream.
///
/// Instructions operate on [`Register`] operands (physical or virtual).
/// The backend lowerer resolves virtual registers through the register cache,
/// folding constants into immediates where possible.
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
    /// Arguments are moved to calling convention registers (x9, x10, ...)
    /// before the call. Return values arrive in the same registers and
    /// are bound to `results` VRegs after the call.
    Call {
        func_idx: FunctionIdx,
        /// VRegs holding call arguments (mapped to x9, x10, ...).
        args: Vec<VReg>,
        /// VRegs to receive return values (mapped from x9, x10, ...).
        results: Vec<VReg>,
        /// Frame pointer advance (bytes) applied before bl and reversed after.
        /// The lowerer flushes dirty registers BEFORE advancing the frame pointer,
        /// ensuring stores go to the correct canonical slots.
        frame_advance: u32,
    },

    /// Return from function.
    Return { values: Vec<VReg> },
}

/// Arithmetic and bitwise operations for [`IrInst::Alu`].
///
/// Each variant maps to a corresponding machine instruction (e.g. `add`,
/// `sub`, `and`) during lowering. The backend selects register-register
/// or register-immediate forms based on operand analysis.
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

impl fmt::Display for AluOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AluOp::Add => write!(f, "add"),
            AluOp::Sub => write!(f, "sub"),
            AluOp::Mul => write!(f, "mul"),
            AluOp::And => write!(f, "and"),
            AluOp::Or => write!(f, "or"),
            AluOp::Xor => write!(f, "xor"),
            AluOp::Shl => write!(f, "shl"),
            AluOp::ShrS => write!(f, "shr_s"),
            AluOp::ShrU => write!(f, "shr_u"),
        }
    }
}

/// Comparison operations for [`IrInst::Cmp`].
///
/// The `S` suffix denotes signed comparisons, `U` denotes unsigned.
/// The lowerer emits a flag-setting instruction (e.g. `subs`) and the
/// subsequent [`IrInst::BrIf`] consumes the flags via a condition code.
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

impl fmt::Display for CmpOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CmpOp::Eq => write!(f, "eq"),
            CmpOp::Ne => write!(f, "ne"),
            CmpOp::LtS => write!(f, "lt_s"),
            CmpOp::LtU => write!(f, "lt_u"),
            CmpOp::GtS => write!(f, "gt_s"),
            CmpOp::GtU => write!(f, "gt_u"),
            CmpOp::LeS => write!(f, "le_s"),
            CmpOp::LeU => write!(f, "le_u"),
            CmpOp::GeS => write!(f, "ge_s"),
            CmpOp::GeU => write!(f, "ge_u"),
        }
    }
}
