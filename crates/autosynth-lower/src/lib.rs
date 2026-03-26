//! Lowering context and operand resolution.
//!
//! This crate bridges the IR and the backend. It provides:
//! - [`LowerCtx`] — the context trait that the orchestrator implements
//! - Operand resolution functions that query the context to fold
//!   immediates or allocate physical registers
//! - [`trace!`] / [`trace_do!`] — feature-gated structured trace emission

use std::cell::Cell;
use std::collections::HashMap;
use std::fmt;

pub mod trace;

// Re-export serde_json so the trace! macro can reference it from
// downstream crates via $crate::__serde_json::json!().
#[cfg(feature = "trace")]
#[doc(hidden)]
pub use serde_json as __serde_json;

#[cfg(feature = "trace")]
use std::cell::RefCell;

use autosynth_ir::VReg;
use autosynth_isa::{IsaReg, PReg, PRegOr, Width};

// --- Instruction group tracking (trace-only) ---
//
// Groups form a dot-separated hierarchy: "7" is the base group for
// IR instruction 7, "7.0" and "7.1" are sub-groups (e.g. individual
// convergence operations within that instruction).
//
// The lowerer calls `set_group(ir_index)` before each instruction.
// Convergence and other multi-step operations use `push_subgroup()`
// / `pop_subgroup()` to create child groups. The backend saves and
// restores the group string on deferred Operations so ASM events
// carry the correct parent through fused instruction paths.
//
// All group tracking compiles to nothing without the `trace` feature.

#[cfg(feature = "trace")]
struct GroupLevel {
    name: String,
    next_child: usize,
}

#[cfg(feature = "trace")]
thread_local! {
    static GROUP_STACK: RefCell<Vec<GroupLevel>> = const { RefCell::new(Vec::new()) };
}

/// Set the base group path for the current IR instruction.
/// Path format: `"func:0:block:U3:ir:18"`
#[cfg(feature = "trace")]
pub fn set_group(path: &str) {
    GROUP_STACK.with(|s| {
        let mut s = s.borrow_mut();
        s.clear();
        s.push(GroupLevel { name: path.to_string(), next_child: 0 });
    });
}

/// Get the current group string (e.g. "7" or "7.1").
#[cfg(feature = "trace")]
pub fn current_group() -> String {
    GROUP_STACK.with(|s| {
        s.borrow().last().map(|l| l.name.clone()).unwrap_or_else(|| "0".to_string())
    })
}

/// Push a new child sub-group under the current group.
/// Creates paths like `"ir:18:conv:0"`, `"ir:18:conv:1"`.
#[cfg(feature = "trace")]
pub fn push_subgroup(label: &str) {
    GROUP_STACK.with(|s| {
        let mut s = s.borrow_mut();
        if s.is_empty() {
            s.push(GroupLevel { name: "ir:0".to_string(), next_child: 0 });
        }
        let parent = &s.last().unwrap().name;
        let child = s.last().unwrap().next_child;
        let name = format!("{parent}:{label}:{child}");
        s.last_mut().unwrap().next_child += 1;
        s.push(GroupLevel { name, next_child: 0 });
    });
}

/// Pop back to the parent group.
#[cfg(feature = "trace")]
pub fn pop_subgroup() {
    GROUP_STACK.with(|s| s.borrow_mut().pop());
}

/// Restore a previously saved group string (used by the backend
/// when replaying deferred instructions).
#[cfg(feature = "trace")]
pub fn restore_group(group: &str) {
    GROUP_STACK.with(|s| {
        let mut s = s.borrow_mut();
        s.clear();
        s.push(GroupLevel { name: group.to_string(), next_child: 0 });
    });
}

/// The context a backend uses to resolve operands and emit machine code.
///
/// Implemented by the orchestrator. The backend calls:
/// - Resolution methods to get physical registers for operands
/// - [`emit_code`](Self::emit_code) to push machine code into the buffer
///
/// The backend never touches virtual registers, the register cache,
/// or spill logic directly — everything goes through this trait.
/// Result of resolving a virtual register — either already in a
/// physical register, or a known constant whose materialization
/// can be deferred.
#[cfg_attr(feature = "trace", derive(serde::Serialize))]
pub enum ResolvedVReg {
    /// Value is in a physical register, ready to use.
    PReg(PReg, Width),
    /// Value is a known constant — the caller decides whether to
    /// fold it as an immediate or materialize into a register.
    Const(i64, Width),
}

pub trait LowerCtx {
    /// Resolve a virtual register to a physical register or constant.
    ///
    /// If the vreg is cached or needs a load, returns `PReg`.
    /// If the vreg is a known constant, returns `Const` so the
    /// caller can attempt immediate folding before materializing.
    fn resolve_vreg(
        &mut self,
        vreg: VReg,
        backend: &mut impl BackendEmitter,
    ) -> Result<ResolvedVReg, LowerError>;

    /// Allocate a physical register for a definition (output).
    /// Returns the register and its width (from the vreg definition).
    ///
    /// If a target constraint requires evicting a dirty vreg, the
    /// implementation uses the backend to emit the spill store.
    fn define_vreg(
        &mut self,
        vreg: VReg,
        backend: &mut impl BackendEmitter,
    ) -> Result<(PReg, Width), LowerError>;

    /// Allocate a free physical register.
    fn alloc_reg(&mut self) -> Result<PReg, LowerError>;
}

/// Extension trait — convenience methods auto-implemented for all
/// [`LowerCtx`] implementors.
///
/// These compose the core `LowerCtx` methods to handle common operand
/// resolution patterns (folding immediates, forcing into registers, etc.).
pub trait LowerCtxExt: LowerCtx {
    /// Try to fold a VReg as an immediate of type `Imm`, falling back
    /// to a physical register if the constant doesn't fit or the VReg
    /// isn't a constant.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// match ctx.try_imm_or_preg::<UImm12>(rhs_vreg) {
    ///     PRegOr::Imm(imm) => { /* emit immediate form */ }
    ///     PRegOr::PReg(reg) => { /* emit register form */ }
    /// }
    /// ```
    fn try_imm_or_preg<Imm>(
        &mut self,
        vreg: VReg,
        backend: &mut impl BackendEmitter,
    ) -> Result<PRegOr<Imm>, LowerError>
    where
        Imm: TryFrom<i64>,
    {
        match self.resolve_vreg(vreg, backend)? {
            ResolvedVReg::PReg(preg, w) => Ok(PRegOr::PReg(preg, w)),
            ResolvedVReg::Const(val, w) => match Imm::try_from(val) {
                Ok(imm) => Ok(PRegOr::Imm(imm)),
                Err(_) => {
                    let preg = self.alloc_reg()?;
                    backend.materialize_const(preg, val, w)?;
                    Ok(PRegOr::PReg(preg, w))
                }
            },
        }
    }

    /// Force a VReg into a physical register, returning its width.
    ///
    /// Constants are materialized into a scratch register.
    fn into_preg(
        &mut self,
        vreg: VReg,
        backend: &mut impl BackendEmitter,
    ) -> Result<(PReg, Width), LowerError> {
        match self.resolve_vreg(vreg, backend)? {
            ResolvedVReg::PReg(preg, w) => Ok((preg, w)),
            ResolvedVReg::Const(val, w) => {
                let preg = self.alloc_reg()?;
                backend.materialize_const(preg, val, w)?;
                Ok((preg, w))
            }
        }
    }

}

impl<T: LowerCtx> LowerCtxExt for T {}

// --- Machine configuration and backend trait ---

/// Machine configuration — register pool and architectural register mapping.
///
/// A physical register with its reservation state.
#[derive(Debug, Clone, Copy)]
pub struct PRegEntry {
    pub preg: PReg,
    pub reserved: bool,
}

/// Machine configuration — physical register pool and architecture info.
///
/// Created by the backend with all registers unreserved except ISA-fixed
/// ones. The frontend reserves registers via [`reserve`](Self::reserve).
#[derive(Debug, Clone)]
pub struct MachineConfig {
    regs: Vec<PRegEntry>,
    isa_regs: HashMap<IsaReg, PReg>,
    stack_alignment: u32,
}

impl MachineConfig {
    pub fn new(all_regs: Vec<PReg>, isa_regs: HashMap<IsaReg, PReg>, stack_alignment: u32) -> Self {
        let mut regs: Vec<PRegEntry> = all_regs
            .into_iter()
            .map(|preg| PRegEntry {
                preg,
                reserved: isa_regs.values().any(|&r| r == preg),
            })
            .collect();
        // Sort by preg number for consistent indexing.
        regs.sort_by_key(|r| r.preg.0);
        Self { regs, isa_regs, stack_alignment }
    }

    /// Reserve a register by role. ISA roles look up the mapping,
    /// FromEnd/FromStart pick from the unreserved pool.
    pub fn reserve(&mut self, role: IsaReg) -> PReg {
        match role {
            IsaReg::FromEnd => {
                let entry = self.regs.iter_mut().rev()
                    .find(|r| !r.reserved)
                    .expect("no registers left");
                entry.reserved = true;
                entry.preg
            }
            IsaReg::FromStart => {
                let entry = self.regs.iter_mut()
                    .find(|r| !r.reserved)
                    .expect("no registers left");
                entry.reserved = true;
                entry.preg
            }
            role => {
                let preg = *self.isa_regs.get(&role)
                    .unwrap_or_else(|| panic!("no ISA register mapping for {role:?}"));
                if let Some(entry) = self.regs.iter_mut().find(|r| r.preg == preg) {
                    entry.reserved = true;
                }
                preg
            }
        }
    }

    /// The unreserved (scratch) registers.
    pub fn scratch_pool(&self) -> Vec<PReg> {
        self.regs.iter().filter(|r| !r.reserved).map(|r| r.preg).collect()
    }

    /// All register entries.
    pub fn regs(&self) -> &[PRegEntry] {
        &self.regs
    }

    pub fn stack_alignment(&self) -> u32 {
        self.stack_alignment
    }

    pub fn num_regs(&self) -> usize {
        self.regs.len()
    }
}

/// Errors that can occur during lowering.
#[derive(Debug)]
pub enum LowerError {
    /// An offset is not aligned to the required boundary.
    MisalignedOffset,
    /// An immediate value is out of the encodable range.
    ImmediateOutOfRange,
    /// No physical registers available for allocation.
    RegPoolExhausted,
    /// A vreg was referenced before being defined.
    UndefinedVReg(VReg),
    /// A vreg was defined more than once.
    DuplicateDefine(VReg),
    /// define_vreg called on a vreg that isn't pending.
    UnexpectedDefine(VReg),
}

impl fmt::Display for LowerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LowerError::MisalignedOffset => write!(f, "misaligned offset"),
            LowerError::ImmediateOutOfRange => write!(f, "immediate out of range"),
            LowerError::RegPoolExhausted => write!(f, "register pool exhausted"),
            LowerError::UndefinedVReg(v) => write!(f, "vreg {v} used before definition"),
            LowerError::DuplicateDefine(v) => write!(f, "vreg {v} defined more than once"),
            LowerError::UnexpectedDefine(v) => write!(f, "define on vreg {v} that isn't pending"),
        }
    }
}

impl std::error::Error for LowerError {}

/// Controls whether the backend buffers an instruction for fusion
/// or emits it immediately.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Emit {
    /// Try to fuse with the next instruction (default for IR stream).
    Fuse,
    /// Flush pending buffer first, then emit immediately.
    /// Used by the register allocator for moves/stores/loads.
    Immediate,
}

/// A backend that lowers IR instructions into machine code.
///
/// The backend is responsible for **instruction selection** — it picks
/// which machine instructions to emit for a given IR operation and
/// pushes them into the code buffer via [`LowerCtx::emit_code`].
///
/// Backends are stateful — they may buffer pending instructions for
/// fusion (e.g. combining an ALU operation with a subsequent branch).
/// The orchestrator calls [`flush`](Self::flush) at block boundaries
/// to ensure all buffered instructions are emitted.
pub trait BackendEmitter: Sized {
    /// Create a new backend instance.
    fn new() -> Self;

    /// Return the default machine configuration for this architecture.
    fn machine_config() -> MachineConfig;

    /// Lower a single IR instruction into machine code.
    ///
    /// If `emit` is [`Emit::Fuse`], the backend may buffer the
    /// instruction for fusion with the next one.
    /// If `emit` is [`Emit::Immediate`], the backend flushes any
    /// pending buffer first, then emits this instruction immediately
    /// (no buffering).
    fn lower(
        &mut self,
        ctx: &mut impl LowerCtx,
        inst: autosynth_ir::IrInst,
        emit: Emit,
    ) -> Result<(), LowerError>;

    /// Flush any pending instructions at block boundaries.
    fn flush(&mut self, ctx: &mut impl LowerCtx) -> Result<(), LowerError>;

    /// Record that `block` starts at the current code offset.
    ///
    /// Called by the lowerer at the start of each block, after flushing
    /// any pending instructions from the previous block. Used by
    /// [`finalize`](Self::finalize) to resolve branch targets.
    fn bind_label(&mut self, block: autosynth_ir::BlockId);

    /// Patch branch and call offsets after all blocks are laid out.
    ///
    /// Called once after all blocks have been emitted. The backend uses
    /// saved instruction offsets and [`LowerCtx::resolve_block`] /
    /// [`LowerCtx::resolve_func`] to compute displacements, then
    /// [`LowerCtx::patch_code`] to overwrite the placeholder offsets.
    fn finalize(&mut self, ctx: &mut impl LowerCtx) -> Result<(), LowerError>;

    /// Materialize a constant into a physical register.
    ///
    /// Returns the register and its width.
    fn materialize_const(&mut self, preg: PReg, val: i64, width: Width) -> Result<(), LowerError>;

    /// The emitted machine code buffer.
    fn code(&self) -> &[u8];
}
