pub mod aarch64;

use crate::ir::Register;
use crate::ir::function::{IRFunction, IsaReg};

/// A physical register on the target architecture.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PhysReg(pub u8);

/// Backend that owns the register pool and lowers IR to machine code.
pub trait BackendEmitter {
    /// Reserve a register for a named ISA role.
    ///
    /// Fixed roles (FramePointer, StackPointer, ReturnAddress) map to
    /// arch-specific registers. Define64 requests consume from the
    /// remaining pool (positive index from start, negative from end).
    /// Returns a `Register::Phys` that can be used in IR instructions.
    fn use_isa_reg(&mut self, name: &'static str, role: IsaReg) -> Register;

    /// The remaining physical registers available for the register allocator.
    fn scratch(&self) -> &[PhysReg];

    /// Lower an IR function to machine code bytes.
    fn lower(&self, func: &IRFunction) -> Vec<u8>;
}
