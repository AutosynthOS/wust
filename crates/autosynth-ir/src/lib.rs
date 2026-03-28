#![no_std]
//! IR types for the autosynth compiler pipeline.
//!
//! Plain data types — no lowering logic, no backend awareness.
//! Resolution methods live in [`autosynth-lower`].

extern crate alloc;

use alloc::boxed::Box;
use alloc::collections::VecDeque;
use alloc::vec::Vec;
use core::fmt;

use autosynth_isa::{PReg, Width};

/// Virtual register identifier.
///
/// Tagged by kind: [`Def`](VReg::Def) is a real value produced by an
/// instruction, [`Ref`](VReg::Ref) is an indirection created at block
/// entry when cloning region state from a predecessor.
///
/// Each variant's `u32` indexes into a separate metadata table
/// (`vreg_defs`, `vreg_refs`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "trace", derive(serde::Serialize))]
pub enum VReg {
    /// A real definition — produced by an instruction, constant, or physical register.
    Def(u32),
    /// Indirection — created at block entry when cloning region state.
    /// Metadata in [`VRegRef`] determines whether this is a direct
    /// alias or a phi (merge of multiple predecessors).
    Ref(u32),
}

impl fmt::Display for VReg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VReg::Def(id) => write!(f, "v{id}"),
            VReg::Ref(id) => write!(f, "r{id}"),
        }
    }
}

/// Identifies a basic block within a function.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "trace", derive(serde::Serialize))]
pub enum BlockId {
    /// Function entry / prologue block.
    Entry,
    /// Caller-defined block, keyed by a source-level index (e.g. program counter).
    User(u32),
    /// Generated block (suspend stubs, cold paths, trampolines).
    Gen(u32),
    /// Shared native epilogue — restores lr, sp, and returns.
    Epilogue,
}

impl fmt::Display for BlockId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BlockId::Entry => write!(f, "E0"),
            BlockId::User(n) => write!(f, "U{n}"),
            BlockId::Gen(n) => write!(f, "G{n}"),
            BlockId::Epilogue => write!(f, "Ep"),
        }
    }
}

/// Index identifying a function in the compilation unit.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "trace", derive(serde::Serialize))]
pub enum FunctionIdx {
    /// A user-defined function, indexed by its position in the module.
    User(u32),
}

/// WASM value type for the IR layer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "trace", derive(serde::Serialize))]
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
#[cfg_attr(feature = "trace", derive(serde::Serialize))]
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
#[cfg_attr(feature = "trace", derive(serde::Serialize))]
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
#[cfg_attr(feature = "trace", derive(serde::Serialize))]
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
#[cfg_attr(feature = "trace", derive(serde::Serialize))]
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
#[cfg_attr(feature = "trace", derive(serde::Serialize))]
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
    /// Emits load from memory or materializes a const if needed.
    /// Used with set_target to ensure a vreg ends up in a specific
    /// physical register.
    Resolve { vreg: VReg },
}

/// A combined instruction for the lowering pipeline.
///
/// The register allocator processes this stream linearly. `Ir` instructions
/// are forwarded to the backend after vreg resolution. `Reg` instructions
/// update the allocator's internal state (no code emitted).
#[derive(Debug, Clone)]
#[cfg_attr(feature = "trace", derive(serde::Serialize))]
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
#[cfg_attr(feature = "trace", derive(serde::Serialize))]
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
#[cfg_attr(feature = "trace", derive(serde::Serialize))]
pub enum VInit {
    /// A compile-time constant (sign-extended to 64 bits). Rematerializable.
    Const(i64),
    /// Value arrived in a physical register (function params, call results).
    PReg(PReg),
    /// Produced as the destination of an instruction (ALU, load, etc.).
    InstDst,
    /// Value lives in memory at [slot.base + slot.offset]. Created after
    /// clobber to start a fresh vreg lifetime — the regalloc reloads on
    /// first use.
    Mem(SlotRef),
}

/// Metadata for a virtual register definition.
///
/// Each VReg has a unique id and a width. The origin (how the value
/// was produced) is communicated via `RegInst::Define` in the
/// instruction stream.
#[derive(Debug, Clone, Copy)]
#[cfg_attr(feature = "trace", derive(serde::Serialize))]
pub struct VRegDef {
    /// The unique virtual register identifier.
    pub id: VReg,
    /// Register width (W32 or W64) — determines instruction width and slot size.
    pub width: Width,
    /// If set, the allocator should place this vreg in this preg.
    /// Used for call args and return values.
    pub target: Option<PReg>,
}

/// How a [`VRegRef`] obtains its value.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "trace", derive(serde::Serialize))]
pub enum VRegRefSource {
    /// Direct alias — single predecessor, resolves straight through.
    Direct(VReg),
    /// Merge point — multiple predecessors provide different values.
    /// Each entry is (predecessor_block, source_vreg).
    Phi(Vec<(BlockId, VReg)>),
}

/// Metadata for a [`VReg::Ref`] — an indirection to another VReg.
///
/// Created at block entry when cloning predecessor region state.
/// Starts as [`VRegRefSource::Direct`] and may be upgraded to
/// [`VRegRefSource::Phi`] when additional predecessors merge in.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "trace", derive(serde::Serialize))]
pub struct VRegRef {
    /// The ref's own identifier (always [`VReg::Ref`]).
    pub id: VReg,
    /// Register width.
    pub width: Width,
    /// How this ref obtains its value.
    pub source: VRegRefSource,
}

impl fmt::Display for VRegRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.source {
            VRegRefSource::Direct(src) => write!(f, "{}->{}", self.id, src),
            VRegRefSource::Phi(sources) => {
                write!(f, "{}\u{2192}", self.id)?;
                for (i, (_, vreg)) in sources.iter().enumerate() {
                    if i > 0 {
                        write!(f, ",")?;
                    }
                    write!(f, "{vreg}")?;
                }
                Ok(())
            }
        }
    }
}

/// Chase through Direct refs to find the root VReg.
/// Phi refs are first-class and returned as-is.
pub fn resolve_ref(vreg: VReg, refs: &[VRegRef]) -> VReg {
    match vreg {
        VReg::Def(_) => vreg,
        VReg::Ref(id) => match &refs[id as usize].source {
            VRegRefSource::Direct(src) => resolve_ref(*src, refs),
            VRegRefSource::Phi(_) => vreg,
        },
    }
}

/// A named region of memory anchored to a register + offset.
///
/// Used for both stack-like regions (push/pop) and struct-like regions
/// (indexed field access). The access pattern is determined by which
/// builder methods the caller uses, not by this config.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "trace", derive(serde::Serialize))]
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

// ---- VCode pipeline types ----

/// Virtual register ID for the VCode pipeline.
///
/// A simple index — metadata (width, origin) lives in a side table.
/// Every value flowing through the pipeline has a unique VRegId.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VRegId(pub u32);

/// An operand on the VCode operand stack.
///
/// Operands are separate from instructions — each VCode instruction
/// implicitly consumes and produces operands based on its arity.
/// The instruction selector transforms operands to make them
/// concrete for the target architecture (e.g. folding a Const as
/// an immediate, emitting a load for a Mem operand).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Operand {
    Const(i64),
    VReg(VRegId),
    PReg(PReg),
    Mem(SlotRef),
    UImm12(autosynth_isa::UImm12),
}

// ---- VCode: new pipeline instruction set ----

/// Virtual-code instruction — the shared instruction type for the
/// select → regalloc → emit pipeline.
///
/// Instructions are pure operation tags. Operands live on a separate
/// stack and are consumed implicitly based on the instruction's arity.
/// The instruction selector transforms operands (e.g. folding constants
/// as immediates) without changing the instruction itself.
///
/// High-level VCode (emitted by the frontend) and low-level VCode
/// (after selection) share this enum. The selector reduces high-level
/// operations into sequences of lower-level ones when needed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VCode {
    /// Arithmetic / logic / comparison: consumes 2 operands (lhs, rhs),
    /// pushes 1 result (dst). The selector resolves operand forms
    /// (register vs immediate) based on the target architecture.
    Alu { op: AluOp },

    /// Compare-and-branch: consumes 2 operands (lhs, rhs), compares
    /// with `op`, and branches. Fused from Alu(Comp) + BrIf at the
    /// wasm builder level.
    BrIf {
        op: CompOp,
        block_if: BlockId,
        block_else: BlockId,
    },

    /// Unconditional branch.
    Branch { target: BlockId },

    /// Function call: consumes N operands (args). The frontend is
    /// responsible for emitting saves/restores around this.
    Call { func_idx: FunctionIdx },

    /// Load from memory: consumes 1 operand (base), pushes 1 result.
    Load { offset: u32, width: Width },

    /// Store to memory: consumes 2 operands (value, base).
    Store { offset: u32, width: Width },

    /// Move / copy: consumes 1 operand (src), pushes 1 result (dst).
    /// Used for register-to-register moves, CC setup, etc.
    Move,

    /// Materialize a constant into a register.
    /// Operands: [Const(val), VReg(dst)] or [Const(val), PReg(dst)].
    /// The emitter encodes this as movz/movk (ARM64), mov imm (x86), etc.
    Materialize,

    /// Return from function. Consumes 0..N operands (results).
    Return,
}

// ---- CodeCtx ----

/// A bag of VCode instructions and operands.
///
/// Used as both input and output for selector/regalloc passes.
/// Error from CodeCtx operations.
#[derive(Debug)]
pub enum CompileError {
    OperandUnderflow,
    RegPoolExhausted,
}

pub struct CodeCtx {
    pub vcode: VecDeque<VCode>,
    pub operands: VecDeque<Operand>,
}

impl CodeCtx {
    pub fn new() -> Self {
        Self {
            vcode: VecDeque::new(),
            operands: VecDeque::new(),
        }
    }

    pub fn from(vcode: VecDeque<VCode>, operands: Vec<Operand>) -> Self {
        Self {
            vcode,
            operands: VecDeque::from(operands),
        }
    }

    pub fn next_operand(&mut self) -> Result<Operand, CompileError> {
        self.operands
            .pop_front()
            .ok_or(CompileError::OperandUnderflow)
    }
}
