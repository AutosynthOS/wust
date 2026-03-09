#![no_std]
//! IR types for the autosynth compiler pipeline.
//!
//! Plain data types — no lowering logic, no backend awareness.
//! Resolution methods live in [`autosynth-lower`].

extern crate alloc;

use alloc::boxed::Box;
use alloc::vec::Vec;
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
    /// A constant 32-bit integer.
    ConstI32(i32),
    /// A constant 64-bit integer.
    ConstI64(i64),
}

impl Operand {
    pub fn width(&self) -> Width {
        match self {
            Operand::VReg(_, w) | Operand::PReg(_, w) => *w,
            Operand::ConstI32(_) => Width::W32,
            Operand::ConstI64(_) => Width::W64,
        }
    }
}

impl fmt::Display for Operand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Operand::VReg(v, _) => write!(f, "{v}"),
            Operand::PReg(p, _) => write!(f, "p{}", p.0),
            Operand::ConstI32(n) => write!(f, "#{n}"),
            Operand::ConstI64(n) => write!(f, "#{n}"),
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FunctionIdx {
    /// A user-defined function, indexed by its position in the module.
    User(u32),
}

/// WASM value type for the IR layer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IrType {
    I32,
    I64,
}

impl IrType {
    /// The register width for this type.
    pub fn width(self) -> Width {
        match self {
            IrType::I32 => Width::W32,
            IrType::I64 => Width::W64,
        }
    }
}

impl fmt::Display for IrType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IrType::I32 => write!(f, "i32"),
            IrType::I64 => write!(f, "i64"),
        }
    }
}

/// Calling convention for a function.
///
/// Every function parameter has a canonical slot on the wasm stack.
/// The Abi determines whether params and results are *also* passed
/// in registers as an optimization, or exclusively through the stack.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Abi {
    /// Params and results are passed in scratch registers, indexed
    /// by position. Param 0 and result 0 share the same register.
    /// Used for direct JIT-to-JIT calls on the hot path.
    ///
    /// All available scratch registers are consumed for params and
    /// results. Any overflow beyond the physical register pool is
    /// flushed to the corresponding canonical stack slot.
    NativeWasm,
    /// No registers — params and results are read from and written
    /// to their canonical wasm stack slots directly. Used for entry
    /// trampolines and resume points where the stack is the source
    /// of truth.
    StackWasm,
}

/// Describes a function's parameter and return types.
///
/// Param and result indices are zero-based. Under [`Abi::NativeWasm`],
/// index 0 maps to the first calling-convention register (e.g. x9),
/// index 1 to the next, and so on. Params and results share the same
/// register slots — a call pops params and pushes results into the
/// same positions.
#[derive(Debug, Clone)]
pub struct FunctionSignature {
    pub abi: Abi,
    pub params: Vec<IrType>,
    pub results: Vec<IrType>,
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

    /// Conditional branch — branch based on a preceding comparison.
    ///
    /// The condition comes from a prior `Alu(Comp)` that sets flags.
    /// The backend consumes the pending flags and emits the appropriate
    /// conditional branch instruction.
    BrIf {
        cond: VReg,
        block_if: BlockId,
        block_else: BlockId,
    },

    /// Unconditional branch.
    Branch { target: BlockId },

    /// Function call (branch-and-link to another function).
    Call { func_idx: FunctionIdx },

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

    /// Return from function (machine-level `ret`).
    ///
    /// The orchestrator handles moving results into return registers
    /// and flushing dirty state before emitting this.
    Return,

    /// Register-to-register move: dst = src.
    ///
    /// Used by the orchestrator for calling convention setup (moving
    /// values into/out of argument registers).
    Move { dst: Register, src: Register },

    /// An instruction that was eliminated during optimization (e.g.
    /// fallthrough branch elimination). Kept in the instruction list
    /// so that IR instruction indices stay aligned with debugger groups.
    Skipped(Box<IrInst>),
}

/// Index into the function builder's vstack table.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VStackId(pub u32);


/// Canonical memory location for a VReg — where it lives on the stack.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CanonSlot {
    /// Which virtual stack this slot belongs to.
    pub vstack: VStackId,
    /// Slot index within that vstack.
    pub index: u32,
    /// Byte offset from the vstack's base (base_reg + base_offset + slot_offset).
    pub byte_offset: u32,
    /// Size in bytes (4 for i32/f32, 8 for i64/f64, 16 for v128).
    pub size: u8,
}

/// Metadata for a virtual register definition.
///
/// Each VReg has a unique id, a width that determines register size and
/// memory layout, an optional canonical stack slot, and an optional
/// initial operand describing how it gets its value.
///
/// When `slot` is `None`, the VReg is a **temp** — it has no canonical
/// memory location and cannot be spilled. Temps must be either consumed
/// immediately (e.g. a comparison result feeding the next `BrIf`) or
/// rematerializable from their `initial` value (e.g. a constant).
#[derive(Debug, Clone, Copy)]
pub struct VRegDef {
    /// The unique virtual register identifier.
    pub id: VReg,
    /// Register width (W32 or W64) — determines instruction width and slot size.
    pub width: Width,
    /// Canonical memory location on a virtual stack, or `None` for temps.
    pub slot: Option<CanonSlot>,
    /// Initial value of this VReg, or `None` if written by an instruction
    /// (ALU result, call return, etc.).
    pub initial: Option<Operand>,
    /// Register placement constraint for the allocator.
    /// - `Some(PReg(..))`: must be in this physical register (CC constraints).
    /// - `Some(VReg(..))`: coalesce — try to share the same physical register.
    /// - `None`: allocator chooses freely.
    pub target: Option<Register>,
}

/// Immutable configuration of a virtual stack — anchored to a register + offset.
///
/// This is the part of a vstack that never changes: which register it's
/// relative to and where it starts. The mutable state (depth, slot
/// assignments) lives on the block builder.
#[derive(Debug, Clone)]
pub struct VStackConfig {
    pub id: VStackId,
    /// Display label for this stack (e.g. "locals", "operands").
    pub label: &'static str,
    /// The register this stack is relative to (always Phys in practice).
    pub base: Register,
    /// Byte offset from the base register to the start of this stack.
    pub base_offset: u32,
}

/// A complete IR function — the finalized output of FunctionBuilder.
///
/// This is a read-only type. All mutation happens during building.
/// Blocks have their params, results, and successors computed.
#[derive(Debug)]
pub struct IRFunction {
    /// Virtual stack configurations (base register + offset per vstack).
    pub vstacks: Vec<VStackConfig>,
    /// All VReg definitions, indexed by VReg id.
    pub vreg_defs: Vec<VRegDef>,
    /// All blocks with analyzed control flow.
    pub blocks: Vec<IrBlock>,
}

/// A basic block in the IR.
///
/// Blocks have typed params (live-in values from predecessors) and
/// results (live-out values passed to successors). At a branch to
/// block B, the brancher provides B's params. At B's terminator,
/// B provides its results to the target block's params.
///
/// This threading makes liveness explicit at every block boundary —
/// the regcache only needs to preserve what's in params/results.
#[derive(Debug)]
pub struct IrBlock {
    /// This block's identifier.
    pub id: BlockId,
    /// Values flowing into this block from predecessors (live-in VRegs).
    pub params: Vec<VReg>,
    /// Values flowing out of this block to successors (live-out VRegs).
    pub results: Vec<VReg>,
    /// Successor block IDs, extracted from the terminator instruction.
    pub successors: Vec<BlockId>,
    /// The instruction stream for this block.
    pub instructions: Vec<IrInst>,
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
            IrInst::Call { func_idx } => {
                write!(f, "call {func_idx}")
            }
            IrInst::Load { dst, base, offset } => {
                write!(f, "{dst} = load [p{}, #{offset}]", base.0)
            }
            IrInst::Store { src, base, offset } => {
                write!(f, "store [p{}, #{offset}], {src}", base.0)
            }
            IrInst::Return => write!(f, "ret"),
            IrInst::Move { dst, src } => write!(f, "{dst} = mov {src}"),
            IrInst::Skipped(inner) => write!(f, "~{inner}"),
        }
    }
}
