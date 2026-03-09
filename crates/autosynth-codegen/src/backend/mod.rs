//! Backend trait and architecture-specific code lowerers.
//!
//! A backend owns the target's register pool, resolves abstract
//! [`IsaReg`] roles to physical registers, and lowers [`IRFunction`]s
//! to native machine code bytes.

/// AArch64 (ARM64) backend implementation.
pub mod aarch64;

pub use autosynth_isa::PReg;

use crate::CodegenError;
use crate::ir::Register;
use crate::ir::function::{IRFunction, IsaReg};

/// Trait for architecture-specific backends that lower IR to machine code.
///
/// The caller reserves registers via [`use_isa_reg`](Self::use_isa_reg)
/// before building the IR, embedding physical register references into
/// instructions. The backend then lowers the complete IR function to
/// native bytes via [`lower`](Self::lower).
pub trait BackendEmitter {
    /// Reserve a physical register for a named ISA role.
    ///
    /// Returns a [`Register::PReg`] that can be used directly in IR instructions.
    fn use_isa_reg(&mut self, name: &'static str, role: IsaReg) -> Register;

    /// Returns the remaining physical registers available for scratch use
    /// by the register allocator.
    fn scratch(&self) -> &[PReg];

    /// Lower a complete IR function to native machine code bytes.
    fn lower(&self, func: &IRFunction) -> Result<Vec<u8>, CodegenError>;
}
