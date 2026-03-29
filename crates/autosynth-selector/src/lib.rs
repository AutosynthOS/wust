#![no_std]

pub use autosynth_ir::{CodeCtx, CompileError};

/// Instruction selector — implemented per backend.
///
/// The selector transforms a VCode stream. What state it holds
/// internally (regalloc, target RegState, etc.) is up to the
/// implementor.
pub trait Selector {
    fn select(&mut self, input: &mut CodeCtx) -> Result<CodeCtx, CompileError>;
}
