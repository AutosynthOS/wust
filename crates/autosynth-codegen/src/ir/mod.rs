//! Intermediate representation types for the codegen pipeline.
//!
//! Core instruction types (`IrInst`, `AluOp`, `Operand`, `Register`, `VReg`,
//! `BlockId`, `FunctionIdx`) are re-exported from [`autosynth_ir`].
//!
//! Types specific to this crate's codegen pipeline (`VStackMut`) are defined here.
//! Data types (`VRegDef`, `CanonSlot`, `VStackId`) are re-exported
//! from [`autosynth_ir`].

pub mod block;
pub mod function;
pub mod instruction;

// Re-export core IR types from autosynth-ir.
pub use autosynth_ir::{
    AluOp, BlockId, CanonSlot, FunctionIdx, Operand, Register, VReg, VRegDef, VStackId,
};

/// Mutable vstack state — depth and slot assignments.
///
/// This is the per-block part of a vstack. It gets cloned at block
/// boundaries (branches snapshot it onto target blocks).
#[derive(Debug, Clone)]
pub struct VStackMut {
    /// Current stack depth (number of occupied slots).
    pub depth: u32,
    /// Slot assignments (index → VReg).
    pub slots: Vec<Option<VReg>>,
}
