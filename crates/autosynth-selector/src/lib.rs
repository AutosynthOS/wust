#![no_std]

use autosynth_regalloc::RegAlloc;

pub use autosynth_ir::{CodeCtx, CompileError};

/// Instruction selector — implemented per backend.
pub trait Selector {
    fn select(
        &mut self,
        regalloc: &mut RegAlloc,
        input: &mut CodeCtx,
    ) -> Result<CodeCtx, CompileError>;
}
