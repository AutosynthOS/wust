#![no_std]
//! IR types for the autosynth compiler pipeline.
//!
//! Plain data types — no lowering logic, no backend awareness.
//! Resolution methods live in [`autosynth-lower`].

extern crate alloc;

use alloc::{format, string::String, vec::Vec};
use core::fmt;

use autosynth_isa::{PReg, Width};

/// Virtual register identifier.
///
/// Assigned during IR construction. The lowerer resolves these to
/// physical registers via the register allocator.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VReg(pub u32);

impl fmt::Display for VReg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "v{}", self.0)
    }
}

/// A register — either virtual (pre-allocation) or physical (post-allocation).
///
/// Carries a [`Width`] so the backend knows whether to use 32-bit or
/// 64-bit instruction forms without querying external metadata.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Register {
    VReg(VReg, Width),
    PReg(PReg, Width),
}

impl Register {
    pub fn width(&self) -> Width {
        match self {
            Register::VReg(_, w) | Register::PReg(_, w) => *w,
        }
    }
}

impl fmt::Display for Register {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Register::VReg(v, _) => write!(f, "{v}"),
            Register::PReg(p, _) => write!(f, "p{}", p.0),
        }
    }
}

/// An instruction operand — a register or a compile-time constant.
///
/// Resolution methods (`try_imm_or_preg`, `into_preg`) are provided
/// by `autosynth-lower` since they require a [`LowerCtx`].
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Operand {
    /// A virtual register — has a canonical stack slot, goes through the cache.
    VReg(VReg, Width),
    /// A physical register — already assigned (fuel, frame pointer, etc.).
    PReg(PReg, Width),
    /// An inline 32-bit constant.
    Imm32(i32),
    /// An inline 64-bit constant.
    Imm64(i64),
}

impl Operand {
    pub fn width(&self) -> Width {
        match self {
            Operand::VReg(_, w) | Operand::PReg(_, w) => *w,
            Operand::Imm32(_) => Width::W32,
            Operand::Imm64(_) => Width::W64,
        }
    }
}

impl fmt::Display for Operand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Operand::VReg(v, _) => write!(f, "{v}"),
            Operand::PReg(p, _) => write!(f, "p{}", p.0),
            Operand::Imm32(n) => write!(f, "#{n}"),
            Operand::Imm64(n) => write!(f, "#{n}"),
        }
    }
}

impl From<Register> for Operand {
    fn from(r: Register) -> Self {
        match r {
            Register::PReg(p, w) => Operand::PReg(p, w),
            Register::VReg(v, w) => Operand::VReg(v, w),
        }
    }
}

/// Identifies a basic block within a function.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BlockId {
    /// Function entry / prologue block.
    Entry,
    /// Caller-defined block, keyed by a source-level index (e.g. program counter).
    User(u32),
    /// Generated block (suspend stubs, cold paths, trampolines).
    Gen(u32),
}

impl fmt::Display for BlockId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BlockId::Entry => write!(f, "E0"),
            BlockId::User(n) => write!(f, "U{n}"),
            BlockId::Gen(n) => write!(f, "G{n}"),
        }
    }
}

/// Index identifying a function in the compilation unit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FunctionIdx {
    /// A user-defined function, indexed by its position in the module.
    User(u32),
}

impl fmt::Display for FunctionIdx {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FunctionIdx::User(n) => write!(f, "fn{n}"),
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
    Comp(CompOp),
}

/// Comparison operations — flag-setting, result usually discarded.
///
/// Emitted as part of [`AluOp::Comp`]. The backend lowers these to
/// flag-setting instructions (e.g. `subs` on ARM64) whose condition
/// codes are consumed by [`IrInst::BrIf`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompOp {
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

impl fmt::Display for CompOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CompOp::Eq => write!(f, "eq"),
            CompOp::Ne => write!(f, "ne"),
            CompOp::LtS => write!(f, "lt_s"),
            CompOp::LtU => write!(f, "lt_u"),
            CompOp::GtS => write!(f, "gt_s"),
            CompOp::GtU => write!(f, "gt_u"),
            CompOp::LeS => write!(f, "le_s"),
            CompOp::LeU => write!(f, "le_u"),
            CompOp::GeS => write!(f, "ge_s"),
            CompOp::GeU => write!(f, "ge_u"),
        }
    }
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
            AluOp::Comp(c) => write!(f, "{c}"),
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

    /// Conditional branch — if cond is truthy, goto block_if, else block_else.
    BrIf {
        cond: VReg,
        block_if: BlockId,
        block_else: BlockId,
    },

    /// Unconditional branch.
    Branch { target: BlockId },

    /// Function call (branch-and-link to another function).
    Call {
        func_idx: FunctionIdx,
        /// VRegs holding call arguments (mapped to x9, x10, ...).
        args: Vec<VReg>,
        /// VRegs to receive return values (mapped from x9, x10, ...).
        results: Vec<VReg>,
        /// Frame pointer advance (bytes) applied before bl and reversed after.
        frame_advance: u32,
    },

    /// Load from memory: dst = [base + offset].
    Load {
        dst: Register,
        base: PReg,
        offset: u32,
    },

    /// Store to memory: [base + offset] = src.
    Store {
        src: Operand,
        base: PReg,
        offset: u32,
    },

    /// Return from function.
    ///
    /// When `flush` is true, the lowerer stores all dirty registers to
    /// their canonical slots before the `ret`.
    Return { values: Vec<VReg>, flush: bool },
}

impl fmt::Display for IrInst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IrInst::Alu { op, dst, lhs, rhs } => {
                write!(f, "{dst} = {op} {lhs}, {rhs}")
            }
            IrInst::BrIf {
                cond,
                block_if,
                block_else,
            } => {
                write!(f, "br_if {cond} then {block_if} else {block_else}")
            }
            IrInst::Branch { target } => {
                write!(f, "br {target}")
            }
            IrInst::Call {
                func_idx,
                args,
                results,
                frame_advance,
            } => {
                let args_s: Vec<String> = args.iter().map(|a| format!("{a}")).collect();
                let res_s: Vec<String> = results.iter().map(|r| format!("{r}")).collect();
                write!(
                    f,
                    "call {func_idx}({}) → ({}) fp+{frame_advance}",
                    args_s.join(", "),
                    res_s.join(", ")
                )
            }
            IrInst::Load { dst, base, offset } => {
                write!(f, "{dst} = load [p{}, #{offset}]", base.0)
            }
            IrInst::Store { src, base, offset } => {
                write!(f, "store [p{}, #{offset}], {src}", base.0)
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
