//! IR instruction types and operator enums.

use std::fmt;

use crate::ir::function::FunctionIdx;

use super::{Register, VReg, VRegDef};
use super::block::BlockId;

/// An operand in an IR instruction — register or inline immediate.
///
/// Unlike [`Register`], an `Operand` can carry a constant value directly.
/// Constants never enter the register cache and never need a stack slot —
/// the lowerer emits them as immediates or rematerializes them as needed.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Operand {
    /// A virtual register — has a canonical stack slot, goes through the cache.
    VReg(VReg),
    /// A physical register — already assigned (fuel, frame pointer, etc.).
    PReg(u8),
    /// An inline 32-bit constant.
    Imm32(i32),
    /// An inline 64-bit constant.
    Imm64(i64),
}

impl fmt::Display for Operand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Operand::VReg(v) => write!(f, "{v}"),
            Operand::PReg(n) => write!(f, "r{n}"),
            Operand::Imm32(n) => write!(f, "#{n}"),
            Operand::Imm64(n) => write!(f, "#{n}"),
        }
    }
}

impl From<VReg> for Operand {
    fn from(v: VReg) -> Self { Operand::VReg(v) }
}

impl From<Register> for Operand {
    fn from(r: Register) -> Self {
        match r {
            Register::Phys(n) => Operand::PReg(n),
            Register::Virtual(id) => Operand::VReg(VReg(id)),
        }
    }
}

/// An IR instruction in the function's instruction stream.
///
/// Instructions operate on [`Operand`]s — virtual registers, physical
/// registers, or inline immediates. The backend lowerer resolves virtual
/// registers through the register cache and emits immediates directly.
#[derive(Debug, Clone)]
pub enum IrInst {
    /// Push a value onto a virtual stack.
    StackPush { def: VRegDef },

    /// Pop a value from a virtual stack.
    StackPop { def: VRegDef },

    /// Arithmetic, logic, or comparison: dst = lhs op rhs.
    ///
    /// For comparison ops (Eq, Ne, LtS, etc.), the result lives in CPU
    /// flags — `dst` is typically the zero register (PReg). The subsequent
    /// [`BrIf`](IrInst::BrIf) consumes the flags via a condition code.
    Alu {
        op: AluOp,
        dst: Register,
        lhs: Operand,
        rhs: Operand,
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
    ///
    /// When `flush` is true, the lowerer stores all dirty registers to
    /// their canonical slots before the `ret`. Used on suspend/unwind
    /// paths where the interpreter needs to read the frame state.
    Return { values: Vec<VReg>, flush: bool },
}

impl fmt::Display for IrInst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IrInst::StackPush { def } => {
                write!(f, "push {} = {}", def.id, def.value)
            }
            IrInst::StackPop { def } => {
                write!(f, "pop {}", def.id)
            }
            IrInst::Alu { op, dst, lhs, rhs } => {
                write!(f, "{dst} = {op} {lhs}, {rhs}")
            }
            IrInst::BrIf { cond, block_if, block_else } => {
                write!(f, "br_if {cond} then {block_if} else {block_else}")
            }
            IrInst::Branch { target } => {
                write!(f, "br {target}")
            }
            IrInst::Call { func_idx, args, results, frame_advance } => {
                let args_s: Vec<String> = args.iter().map(|a| format!("{a}")).collect();
                let res_s: Vec<String> = results.iter().map(|r| format!("{r}")).collect();
                write!(f, "call {func_idx}({}) → ({}) fp+{frame_advance}", args_s.join(", "), res_s.join(", "))
            }
            IrInst::Return { values, flush } => {
                let vals: Vec<String> = values.iter().map(|v| format!("{v}")).collect();
                if *flush {
                    write!(f, "ret {} flush", vals.join(", "))
                } else {
                    write!(f, "ret {}", vals.join(", "))
                }
            }
        }
    }
}

/// Operations for [`IrInst::Alu`].
///
/// Covers arithmetic, logic, shifts, and comparisons. The backend selects
/// register-register or register-immediate forms based on operand analysis.
/// Comparison ops emit flag-setting instructions (e.g. `subs`) whose
/// condition codes are consumed by [`IrInst::BrIf`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AluOp {
    // --- Arithmetic ---
    Add,
    Sub,
    Mul,

    // --- Bitwise logic ---
    And,
    Or,
    Xor,

    // --- Shifts ---
    Shl,
    ShrS,
    ShrU,

    // --- Comparisons (flag-setting, result usually discarded) ---
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

impl AluOp {
    /// True if this op is a comparison (sets flags, result typically discarded).
    pub fn is_comparison(self) -> bool {
        matches!(self, Self::Eq | Self::Ne
            | Self::LtS | Self::LtU | Self::GtS | Self::GtU
            | Self::LeS | Self::LeU | Self::GeS | Self::GeU)
    }
}

impl fmt::Display for AluOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            // Arithmetic
            AluOp::Add => write!(f, "add"),
            AluOp::Sub => write!(f, "sub"),
            AluOp::Mul => write!(f, "mul"),
            // Bitwise logic
            AluOp::And => write!(f, "and"),
            AluOp::Or => write!(f, "or"),
            AluOp::Xor => write!(f, "xor"),
            // Shifts
            AluOp::Shl => write!(f, "shl"),
            AluOp::ShrS => write!(f, "shr_s"),
            AluOp::ShrU => write!(f, "shr_u"),
            // Comparisons
            AluOp::Eq => write!(f, "eq"),
            AluOp::Ne => write!(f, "ne"),
            AluOp::LtS => write!(f, "lt_s"),
            AluOp::LtU => write!(f, "lt_u"),
            AluOp::GtS => write!(f, "gt_s"),
            AluOp::GtU => write!(f, "gt_u"),
            AluOp::LeS => write!(f, "le_s"),
            AluOp::LeU => write!(f, "le_u"),
            AluOp::GeS => write!(f, "ge_s"),
            AluOp::GeU => write!(f, "ge_u"),
        }
    }
}
