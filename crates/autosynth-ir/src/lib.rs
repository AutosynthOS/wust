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

/// Virtual register — a simple index into the regalloc's def table.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "trace", derive(serde::Serialize))]
pub struct VReg(pub u32);

impl fmt::Display for VReg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "v{}", self.0)
    }
}

/// Identifies a basic block within a function.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "trace", derive(serde::Serialize))]
pub enum BlockId {
    /// Function entry blocks. Entry(0) = host trampoline, Entry(1) = body.
    Entry(u32),
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
            BlockId::Entry(n) => write!(f, "E{n}"),
            BlockId::User(n) => write!(f, "U{n}"),
            BlockId::Gen(n) => write!(f, "G{n}"),
            BlockId::Epilogue => write!(f, "Ep"),
        }
    }
}

/// Index identifying a function in the compilation unit.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "trace", derive(serde::Serialize))]
pub enum FunctionIdx {
    /// A user-defined function, indexed by its position in the module.
    User(u32),
}

/// A label identifying a position in emitted code.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "trace", derive(serde::Serialize))]
pub enum Label {
    /// A block within a function.
    Block(FunctionIdx, BlockId),
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
    Define { vreg: VReg, value: VRegState },
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

/// Per-VReg state. Tracks where a value currently lives.
/// Multiple fields can be active simultaneously — a value can be
/// in a register AND in memory AND known as a constant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VRegState {
    pub width: Width,
    pub preg: Option<PReg>,
    pub target: Option<PReg>,
    pub slot: Option<SlotRef>,
    pub dirty: bool,
    pub r#const: Option<i64>,
    pub copy: Option<VReg>,
    pub phi: Option<Vec<VRegSource>>,
    pub inst_dst: bool,
}

impl VRegState {
    pub fn new(width: Width) -> Self {
        Self {
            width,
            preg: None,
            target: None,
            slot: None,
            dirty: true,
            r#const: None,
            copy: None,
            phi: None,
            inst_dst: false,
        }
    }
}

/// A VReg with its source block.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "trace", derive(serde::Serialize))]
pub struct VRegSource {
    pub block: BlockId,
    pub vreg: VReg,
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

/// An operand on the VCode operand stack.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Operand {
    Const(i64),
    VReg(VReg),
    PReg(PReg),
    /// Destination VReg — instruction output, before PReg allocation.
    DstVReg(VReg),
    /// Destination PReg — instruction output, after PReg allocation.
    DstPReg(PReg, Width),
    Mem(SlotRef),
    UImm12(autosynth_isa::UImm12),
    SImm9(autosynth_isa::SImm9),
}

impl From<VReg> for Operand {
    fn from(v: VReg) -> Self {
        Operand::VReg(v)
    }
}

impl From<PReg> for Operand {
    fn from(p: PReg) -> Self {
        Operand::PReg(p)
    }
}

impl From<autosynth_isa::UImm12> for Operand {
    fn from(i: autosynth_isa::UImm12) -> Self {
        Operand::UImm12(i)
    }
}

impl From<autosynth_isa::SImm9> for Operand {
    fn from(i: autosynth_isa::SImm9) -> Self {
        Operand::SImm9(i)
    }
}

impl From<SlotRef> for Operand {
    fn from(s: SlotRef) -> Self {
        Operand::Mem(s)
    }
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
    /// An inline operand (input) in the VCode stream.
    Operand(Operand),

    /// Define — this VReg is live from here. preg_alloc looks up
    /// the VRegState from the allocator to initialize RegState.
    Define(VReg),

    /// Set a VReg's canonical stack slot. Consumed by preg_alloc
    /// to update RegState — no machine code emitted.
    SetSlot { vreg: VReg, slot: SlotRef },

    /// Clear a VReg's canonical stack slot.
    ClearSlot(VReg),

    /// Keep a VReg alive through this point — no code emitted.
    /// Inserted by convergence for phi sources that are already live
    /// but need to survive until the branch. Consumed by preg_alloc.
    KeepAlive,

    /// Arithmetic / logic / comparison.
    Alu { op: AluOp },

    /// Compare-and-branch: fused from Alu(Comp) + BrIf.
    BrIf {
        op: CompOp,
        block_if: BlockId,
        block_else: BlockId,
    },

    /// Unconditional branch.
    Branch { target: BlockId },

    /// Branch-and-link (call). Saves return address, jumps to target label.
    Bl { target: Label },

    /// Load value to memory location
    /// - Operand::PReg -> base
    /// - Operand::Const -> offset
    /// - VCode::Load
    /// - Operand::DstPReg | Operand::DstVReg
    Load,

    /// Store value to memory location
    /// - Operand::PReg -> base
    /// - Operand::Const -> offset
    /// - VCode::Store
    /// - Operand::DstPreg | Operand::DstVreg
    Store,

    /// Move / copy.
    Move,

    /// Materialize a vreg, const or value into a register.
    /// - Operand::Const
    /// - VCode::Clobber
    /// - Operand::DstVReg | Operand::DstPReg
    Materialize,

    /// Return from function.
    Return,

    /// Clobber's a VReg, causing a store instruction to be emitted
    /// if it's still dirty
    /// - VReg
    /// - VCode::Clobber
    Clobber,
}

impl From<Operand> for VCode {
    fn from(op: Operand) -> Self {
        VCode::Operand(op)
    }
}

// ---- CodeCtx ----

/// A bag of VCode instructions and operands.
///
/// Used as both input and output for selector/regalloc passes.
/// Error from compilation — covers selection, regalloc, and emission.
#[derive(Debug)]
pub enum CompileError {
    OperandUnderflow,
    RegPoolExhausted,
    UnresolvedOperand,
    ImmediateOutOfRange,
    UnhandledInstruction,
    UnresolvedLabel,
}

#[derive(Clone)]
pub struct CodeCtx {
    pub stream: VecDeque<VCode>,
}

impl CodeCtx {
    pub fn new() -> Self {
        Self {
            stream: VecDeque::new(),
        }
    }

    pub fn push(&mut self, item: VCode) {
        self.stream.push_back(item);
    }

    pub fn push_operand(&mut self, op: Operand) {
        self.stream.push_back(VCode::Operand(op));
    }

    /// Pop the next non-operand item from the front.
    pub fn next_operand(&mut self) -> Result<Operand, CompileError> {
        match self.stream.pop_front() {
            Some(VCode::Operand(op)) => Ok(op),
            Some(other) => {
                // Put it back — caller expected an operand but got an instruction.
                self.stream.push_front(other);
                Err(CompileError::OperandUnderflow)
            }
            None => Err(CompileError::OperandUnderflow),
        }
    }

    /// Pop the next item from the front (operand or instruction).
    pub fn next(&mut self) -> Option<VCode> {
        self.stream.pop_front()
    }

    /// Pop the last item if it's an operand.
    /// Scan the stream for all VRegs that appear as operands or defines.
    pub fn live_vregs(&self) -> alloc::collections::BTreeSet<VReg> {
        let mut live = alloc::collections::BTreeSet::new();
        for item in &self.stream {
            match item {
                VCode::Operand(Operand::VReg(vreg)) => {
                    live.insert(*vreg);
                }
                _ => {}
            }
        }
        live
    }

    pub fn pop_operand_back(&mut self) -> Result<Operand, CompileError> {
        match self.stream.pop_back() {
            Some(VCode::Operand(op)) => Ok(op),
            Some(other) => {
                self.stream.push_back(other);
                Err(CompileError::OperandUnderflow)
            }
            None => Err(CompileError::OperandUnderflow),
        }
    }

    /// Split into an unzipper that separates instructions from operands.
    pub fn unzip(self) -> CodeCtxUnzipper {
        CodeCtxUnzipper {
            stream: self.stream,
            operands: VecDeque::new(),
            instructions: VecDeque::new(),
        }
    }
}

/// Walks a CodeCtx stream, splitting instructions from operands.
///
/// Each side has a pending buffer. When you ask for an instruction,
/// any operands encountered are buffered. When you ask for an
/// operand, any instructions encountered are buffered. Both sides
/// drain from the same underlying stream.
pub struct CodeCtxUnzipper {
    stream: VecDeque<VCode>,
    operands: VecDeque<Operand>,
    instructions: VecDeque<VCode>,
}

impl CodeCtxUnzipper {
    /// Get the next instruction. Buffers any operands encountered.
    pub fn next_inst(&mut self) -> Option<VCode> {
        if let Some(inst) = self.instructions.pop_front() {
            return Some(inst);
        }
        while let Some(item) = self.stream.pop_front() {
            match item {
                VCode::Operand(op) => self.operands.push_back(op),
                inst => return Some(inst),
            }
        }
        None
    }

    /// Get the next operand. Buffers any instructions encountered.
    pub fn next_operand(&mut self) -> Result<Operand, CompileError> {
        if let Some(op) = self.operands.pop_front() {
            return Ok(op);
        }
        while let Some(item) = self.stream.pop_front() {
            match item {
                VCode::Operand(op) => return Ok(op),
                inst => self.instructions.push_back(inst),
            }
        }
        Err(CompileError::OperandUnderflow)
    }

    /// Get the next operand, expecting a PReg. Errors if not a PReg.
    pub fn expect_preg(&mut self) -> Result<PReg, CompileError> {
        match self.next_operand()? {
            Operand::PReg(preg) => Ok(preg),
            _ => Err(CompileError::UnresolvedOperand),
        }
    }

    /// Get the next operand, expecting a DstPReg. Errors if not a DstPReg.
    pub fn expect_dst(&mut self) -> Result<(PReg, Width), CompileError> {
        match self.next_operand()? {
            Operand::DstPReg(preg, width) => Ok((preg, width)),
            _ => Err(CompileError::OperandUnderflow),
        }
    }
}
