//! Backend trait and architecture-specific code lowerers.
//!
//! A backend owns the target's register pool, resolves abstract
//! [`IsaReg`] roles to physical registers, and lowers [`IRFunction`]s
//! to native machine code bytes.

/// AArch64 (ARM64) backend implementation.
pub mod aarch64;
/// RISC-V 64-bit (RV64I) backend implementation.
pub mod riscv64;
/// x86_64 (AMD64) backend implementation.
pub mod x86;

use crate::CodegenError;
use crate::ir::Register;
use crate::ir::function::{IRFunction, IsaReg};

/// A physical register on the target architecture, identified by its
/// hardware index (e.g. 0–30 for AArch64 general-purpose registers).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PhysReg(pub u8);

/// Trait for architecture-specific backends that lower IR to machine code.
///
/// The caller reserves registers via [`use_isa_reg`](Self::use_isa_reg)
/// before building the IR, embedding physical register references into
/// instructions. The backend then lowers the complete IR function to
/// native bytes via [`lower`](Self::lower).
pub trait BackendEmitter {
    /// Reserve a physical register for a named ISA role.
    ///
    /// Fixed roles ([`FramePointer`](IsaReg::FramePointer),
    /// [`StackPointer`](IsaReg::StackPointer),
    /// [`ReturnAddress`](IsaReg::ReturnAddress)) map to arch-specific
    /// registers. [`Define64`](IsaReg::Define64) requests consume from
    /// the remaining pool (positive index from start, negative from end).
    ///
    /// Returns a [`Register::Phys`] that can be used directly in IR instructions.
    fn use_isa_reg(&mut self, name: &'static str, role: IsaReg) -> Register;

    /// Returns the remaining physical registers available for scratch use
    /// by the register allocator (i.e., those not consumed by [`use_isa_reg`](Self::use_isa_reg)).
    fn scratch(&self) -> &[PhysReg];

    /// Lower a complete IR function to native machine code bytes.
    fn lower(&self, func: &IRFunction) -> Result<Vec<u8>, CodegenError>;
}
