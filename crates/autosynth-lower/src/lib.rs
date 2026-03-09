//! Lowering context and operand resolution.
//!
//! This crate bridges the IR and the backend. It provides:
//! - [`LowerCtx`] — the context trait that the orchestrator implements
//! - Operand resolution functions that query the context to fold
//!   immediates or allocate physical registers

use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;

use autosynth_ir::{BlockId, FunctionIdx, Operand, Register, VReg};
use autosynth_isa::{IsaReg, PReg, PRegOr, Width};

/// Minimal debug sink for machine instruction annotation.
///
/// Implemented by the concrete `Debugger` in `autosynth-codegen`.
/// Access via the thread-local [`dbg`] function — when no debugger
/// is installed, the closure never runs (zero cost).
pub trait DbgSink: core::any::Any {
    /// Activate the group for an IR instruction index.
    ///
    /// Subsequent `emit_machine_inst` / `set_machine` calls will
    /// attach to this group.
    fn begin_ir_inst(&mut self, ir_index: usize);
    /// Begin a new machine instruction row in the current group.
    fn emit_machine_inst(&mut self);
    /// Set a column value on the last machine instruction.
    fn set_machine(&mut self, col: &str, value: &str);

    /// Get the current group index.
    ///
    /// Used by the backend to save the group when deferring an instruction,
    /// so it can be restored later via [`set_current_group`](Self::set_current_group).
    fn current_group(&self) -> usize;

    /// Set the current group index directly.
    ///
    /// Used by the backend to restore a saved group before emitting
    /// a deferred instruction's machine code.
    fn set_current_group(&mut self, group: usize);

    /// Upcast to `Any` for downcasting back to the concrete type.
    fn as_any(self: Box<Self>) -> Box<dyn core::any::Any>;
}

thread_local! {
    static DBG_SINK: RefCell<Option<Box<dyn DbgSink>>> = const { RefCell::new(None) };
}

/// Install a debug sink as the thread-local instance.
pub fn install_dbg(sink: Box<dyn DbgSink>) {
    DBG_SINK.with(|d| *d.borrow_mut() = Some(sink));
}

/// Remove and return the thread-local debug sink.
pub fn take_dbg() -> Option<Box<dyn DbgSink>> {
    DBG_SINK.with(|d| d.borrow_mut().take())
}

/// Run a closure with the thread-local debug sink, if one is installed.
///
/// When no debugger is installed the closure never runs — zero cost.
pub fn dbg(f: impl FnOnce(&mut dyn DbgSink)) {
    DBG_SINK.with(|d| {
        if let Some(sink) = d.borrow_mut().as_mut() {
            f(sink.as_mut());
        }
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
pub trait LowerCtx {
    /// Get the constant value behind a virtual register, if known.
    ///
    /// Returns `None` if the vreg is not a compile-time constant.
    fn const_value(&self, vreg: VReg) -> Option<i64>;

    /// Force a constant into a physical register via materialization
    /// (e.g. `movz`/`movk`). Returns the register and its width.
    fn materialize_const(&mut self, val: i64, width: Width) -> (PReg, Width);

    /// Resolve a virtual register to a physical register.
    /// Returns the register and its width (from the vreg definition).
    ///
    /// If the vreg is not in the cache, the implementation emits a
    /// load from its canonical slot via the backend.
    fn resolve_vreg(&mut self, vreg: VReg, backend: &mut impl BackendEmitter) -> (PReg, Width);

    /// Allocate a physical register for a definition (output).
    /// Returns the register and its width (from the vreg definition).
    ///
    /// If a target constraint requires evicting a dirty vreg, the
    /// implementation uses the backend to emit the spill store.
    fn define_vreg(&mut self, vreg: VReg, backend: &mut impl BackendEmitter) -> (PReg, Width);

    /// Push encoded machine code into the code buffer.
    ///
    /// Returns the byte offset where the code was placed. The backend
    /// can save this offset to patch the instruction later during
    /// [`BackendEmitter::finalize`].
    fn emit_code(&mut self, bytes: &[u8]) -> usize;

    /// Overwrite bytes at a previously emitted offset.
    ///
    /// Used during finalization to patch branch/call offsets after
    /// all blocks have been laid out and their addresses are known.
    fn patch_code(&mut self, offset: usize, bytes: &[u8]);

    /// Resolve a block label to its byte offset in the code buffer.
    ///
    /// Returns `None` if the block hasn't been emitted yet (should
    /// only be called during finalization, after all blocks are laid out).
    fn resolve_block(&self, block: BlockId) -> Option<usize>;

    /// Resolve a function index to its byte offset in the code buffer.
    ///
    /// For self-recursive calls this is 0 (start of the function body).
    fn resolve_func(&self, func_idx: FunctionIdx) -> Option<usize>;
}

/// Extension trait — convenience methods auto-implemented for all
/// [`LowerCtx`] implementors.
///
/// These compose the core `LowerCtx` methods to handle common operand
/// resolution patterns (folding immediates, forcing into registers, etc.).
pub trait LowerCtxExt: LowerCtx {
    /// Try to fold an operand as an immediate of type `Imm`, falling back
    /// to a physical register if the constant doesn't fit or the operand
    /// isn't a constant.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// match ctx.try_imm_or_preg::<UImm12>(&operand) {
    ///     PRegOr::Imm(imm) => { /* emit immediate form */ }
    ///     PRegOr::PReg(reg) => { /* emit register form */ }
    /// }
    /// ```
    fn try_imm_or_preg<Imm>(&mut self, operand: &Operand, backend: &mut impl BackendEmitter) -> PRegOr<Imm>
    where
        Imm: TryFrom<i64>,
    {
        match *operand {
            Operand::ConstI32(val) => match Imm::try_from(val as i64) {
                Ok(imm) => PRegOr::Imm(imm),
                Err(_) => {
                    let (preg, _) = self.materialize_const(val as i64, Width::W32);
                    PRegOr::PReg(preg)
                }
            },
            Operand::ConstI64(val) => match Imm::try_from(val) {
                Ok(imm) => PRegOr::Imm(imm),
                Err(_) => {
                    let (preg, _) = self.materialize_const(val, Width::W64);
                    PRegOr::PReg(preg)
                }
            },
            Operand::VReg(vreg, _) => {
                // Check if the vreg is a known constant that fits.
                if let Some(val) = self.const_value(vreg) {
                    if let Ok(imm) = Imm::try_from(val) {
                        return PRegOr::Imm(imm);
                    }
                }
                let (preg, _) = self.resolve_vreg(vreg, backend);
                PRegOr::PReg(preg)
            }
            Operand::PReg(preg, _) => PRegOr::PReg(preg),
        }
    }

    /// Force an operand into a physical register, returning its width.
    fn into_preg(&mut self, operand: &Operand, backend: &mut impl BackendEmitter) -> (PReg, Width) {
        match *operand {
            Operand::ConstI32(val) => self.materialize_const(val as i64, Width::W32),
            Operand::ConstI64(val) => self.materialize_const(val, Width::W64),
            Operand::VReg(vreg, _) => self.resolve_vreg(vreg, backend),
            Operand::PReg(preg, w) => (preg, w),
        }
    }

    /// Resolve a register (virtual or physical) to a physical register,
    /// returning its width.
    fn resolve_register(&mut self, reg: &Register, backend: &mut impl BackendEmitter) -> (PReg, Width) {
        match *reg {
            Register::VReg(vreg, _) => self.resolve_vreg(vreg, backend),
            Register::PReg(preg, w) => (preg, w),
        }
    }

    /// Allocate a physical register for a register definition, returning
    /// its width.
    fn define_register(
        &mut self,
        reg: &Register,
        backend: &mut impl BackendEmitter,
    ) -> (PReg, Width) {
        match *reg {
            Register::VReg(vreg, _) => self.define_vreg(vreg, backend),
            Register::PReg(preg, w) => (preg, w),
        }
    }
}

impl<T: LowerCtx> LowerCtxExt for T {}

// --- Machine configuration and backend trait ---

/// Machine configuration — register pool and named reservations.
///
/// Created by the backend with the full register pool and
/// arch-specific fixed mappings. The frontend reserves registers
/// by name via [`reserve`](Self::reserve), and the remaining pool
/// is used for scratch allocation. Reserved registers are looked up
/// by name via [`use_reserved`](Self::use_reserved).
#[derive(Clone)]
pub struct MachineConfig {
    /// Available (unreserved) registers.
    pool: Vec<PReg>,
    /// Named reserved registers.
    reserved: HashMap<&'static str, Register>,
    /// Backend-provided mapping from fixed roles to physical registers.
    fixed: fn(IsaReg) -> Option<PReg>,
}

impl MachineConfig {
    pub fn new(pool: Vec<PReg>, fixed: fn(IsaReg) -> Option<PReg>) -> Self {
        Self {
            pool,
            reserved: HashMap::new(),
            fixed,
        }
    }

    /// Reserve a register by name and architectural role.
    ///
    /// Fixed roles (FramePointer, ReturnAddress, StackPointer) map
    /// to platform-specific registers. `Alloc64` allocates from the
    /// remaining pool by index.
    ///
    /// Returns a `Register::PReg` for use in IR instructions.
    ///
    /// # Panics
    ///
    /// Panics if `name` is already reserved.
    pub fn reserve(&mut self, name: &'static str, role: IsaReg) -> Register {
        assert!(
            !self.reserved.contains_key(name),
            "register '{name}' already reserved"
        );
        let preg = if let Some(fixed) = (self.fixed)(role) {
            let len_before = self.pool.len();
            self.pool.retain(|r| *r != fixed);
            assert!(
                self.pool.len() < len_before,
                "register p{} (for '{name}') was already reserved",
                fixed.0
            );
            fixed
        } else {
            let IsaReg::Alloc64(idx) = role else {
                unreachable!()
            };
            if idx >= 0 {
                self.pool.remove(idx as usize)
            } else {
                let pos = self.pool.len() - ((-idx) as usize);
                self.pool.remove(pos)
            }
        };
        let reg = Register::PReg(preg, Width::W64);
        self.reserved.insert(name, reg);
        reg
    }

    /// Look up a reserved register by name.
    ///
    /// # Panics
    ///
    /// Panics if `name` was never reserved.
    pub fn use_reserved(&self, name: &str) -> Register {
        *self
            .reserved
            .get(name)
            .unwrap_or_else(|| panic!("register '{name}' was never reserved"))
    }

    /// The remaining unreserved registers (scratch pool).
    pub fn scratch_pool(&self) -> &[PReg] {
        &self.pool
    }
}

/// Errors that can occur during lowering.
#[derive(Debug)]
pub enum LowerError {
    /// An offset is not aligned to the required boundary.
    MisalignedOffset,
    /// An immediate value is out of the encodable range.
    ImmediateOutOfRange,
}

impl fmt::Display for LowerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LowerError::MisalignedOffset => write!(f, "misaligned offset"),
            LowerError::ImmediateOutOfRange => write!(f, "immediate out of range"),
        }
    }
}

impl std::error::Error for LowerError {}

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
    /// Create a new backend instance with the machine configuration
    /// for this architecture.
    fn new() -> (Self, MachineConfig);

    /// Lower a single IR instruction into machine code.
    fn lower(
        &mut self,
        ctx: &mut impl LowerCtx,
        inst: autosynth_ir::IrInst,
    ) -> Result<(), LowerError>;

    /// Flush any pending instructions at block boundaries.
    fn flush(&mut self, ctx: &mut impl LowerCtx) -> Result<(), LowerError>;

    /// Patch branch and call offsets after all blocks are laid out.
    ///
    /// Called once after all blocks have been emitted. The backend uses
    /// saved instruction offsets and [`LowerCtx::resolve_block`] /
    /// [`LowerCtx::resolve_func`] to compute displacements, then
    /// [`LowerCtx::patch_code`] to overwrite the placeholder offsets.
    fn finalize(&mut self, ctx: &mut impl LowerCtx) -> Result<(), LowerError>;
}
