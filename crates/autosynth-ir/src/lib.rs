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
/// Instructions operate on [`VReg`]s. The backend lowerer resolves virtual
/// registers through the register cache to get physical registers or
/// constants, selecting immediate vs register forms accordingly.
#[derive(Debug, Clone)]
pub enum IrInst {
    /// Arithmetic, logic, or comparison: dst = lhs op rhs.
    ///
    /// All operands are VRegs. The backend resolves them through the
    /// register cache — constants fold as immediates when possible,
    /// physical register bindings resolve directly.
    ///
    /// For comparison ops (Eq, Ne, LtS, etc.), the result lives in CPU
    /// flags — `dst` is typically a VReg bound to the zero register.
    /// The subsequent [`BrIf`](IrInst::BrIf) consumes the flags.
    Alu {
        op: AluOp,
        dst: VReg,
        lhs: VReg,
        rhs: VReg,
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
        dst: PReg,
        width: Width,
        base: PReg,
        offset: u32,
    },

    /// Store to memory: [base + offset] = src.
    Store {
        src: PReg,
        width: Width,
        base: PReg,
        offset: u32,
    },

    /// Return from function (machine-level `ret`).
    ///
    /// The orchestrator handles moving results into return registers
    /// and flushing dirty state before emitting this.
    Return,

    /// Physical register-to-register move: dst = src.
    ///
    /// Used by the orchestrator for calling convention setup (moving
    /// values into/out of argument registers).
    Move {
        dst: PReg,
        dst_width: Width,
        src: PReg,
        src_width: Width,
    },

    /// An instruction that was eliminated during optimization (e.g.
    /// fallthrough branch elimination). Kept in the instruction list
    /// so that IR instruction indices stay aligned with debugger groups.
    Skipped(Box<IrInst>),
}

/// A register allocation instruction — commands to the register allocator.
///
/// These are interleaved with [`IrInst`]s in the [`LowerInst`] stream.
/// The register allocator processes these to maintain its internal state
/// (vreg definitions, slot assignments, liveness, dirtiness).
#[derive(Debug, Clone)]
pub enum RegInst {
    /// Define a new vreg with its initial value origin.
    /// Panics if the vreg has already been defined.
    Define { vreg: VReg, value: VInit },
    /// Assign a canonical memory slot to a vreg (push, set_field).
    /// The slot is always dirty — memory doesn't have the value yet.
    SetSlot { vreg: VReg, slot: SlotRef },
    /// Remove a vreg's canonical slot (pop — value becomes a temp).
    ClearSlot { vreg: VReg, slot: SlotRef },
    /// Store to memory if dirty, then clear the register binding.
    /// Used before calls — the register is about to be destroyed.
    Clobber { vreg: VReg },
    /// Force-resolve a vreg — ensure its value is in a register.
    /// Emits load from memory if needed. Used with set_target to
    /// ensure a vreg ends up in a specific physical register.
    Resolve { vreg: VReg },
}

/// A combined instruction for the lowering pipeline.
///
/// The register allocator processes this stream linearly. `Ir` instructions
/// are forwarded to the backend after vreg resolution. `Reg` instructions
/// update the allocator's internal state (no code emitted).
#[derive(Debug, Clone)]
pub enum LowerInst {
    /// An IR instruction — the backend selects machine instructions for this.
    Ir(IrInst),
    /// A register allocation command — the allocator updates its state.
    Reg(RegInst),
}

/// Index into the virtual region table.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VRegionId(pub u32);

/// A resolved memory location for a vreg slot.
///
/// The builder computes the byte offset at emit time from the
/// region's base register, base offset, and preceding slot widths.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SlotRef {
    /// Base physical register (e.g. frame pointer).
    pub base: PReg,
    /// Byte offset from the base register.
    pub offset: u32,
}

/// Immutable origin of a VReg's value — how it was created.
///
/// SSA: a VReg's value never changes after definition. The origin
/// tells the lowerer how to obtain the value (rematerialize a const,
/// look up a register binding, resolve via the register allocator).
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum VInit {
    /// A compile-time constant (sign-extended to 64 bits). Rematerializable.
    Const(i64),
    /// Value arrived in a physical register (function params, call results).
    PReg(PReg),
    /// Produced as the destination of an instruction (ALU, load, etc.).
    InstDst,
}

/// Metadata for a virtual register definition.
///
/// Each VReg has a unique id and a width. The origin (how the value
/// was produced) is communicated via `RegInst::Define` in the
/// instruction stream.
#[derive(Debug, Clone, Copy)]
pub struct VRegDef {
    /// The unique virtual register identifier.
    pub id: VReg,
    /// Register width (W32 or W64) — determines instruction width and slot size.
    pub width: Width,
    /// If set, the allocator should place this vreg in this preg.
    /// Used for call args and return values.
    pub target: Option<PReg>,
}

/// A named region of memory anchored to a register + offset.
///
/// Used for both stack-like regions (push/pop) and struct-like regions
/// (indexed field access). The access pattern is determined by which
/// builder methods the caller uses, not by this config.
#[derive(Debug, Clone)]
pub struct VRegion {
    /// Display label (e.g. "locals", "operands").
    pub label: &'static str,
    /// The physical register this region is relative to.
    pub base: PReg,
    /// Byte offset from the base register to the start of this region.
    pub base_offset: u32,
    /// Which VReg occupies each slot position in this region.
    pub slots: Vec<VReg>,
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
            IrInst::Load {
                dst, base, offset, ..
            } => {
                write!(f, "p{} = load [p{}, #{offset}]", dst.0, base.0)
            }
            IrInst::Store {
                src, base, offset, ..
            } => {
                write!(f, "store [p{}, #{offset}], p{}", base.0, src.0)
            }
            IrInst::Return => write!(f, "ret"),
            IrInst::Move { dst, src, .. } => write!(f, "p{} = mov p{}", dst.0, src.0),
            IrInst::Skipped(inner) => write!(f, "~{inner}"),
        }
    }
}
