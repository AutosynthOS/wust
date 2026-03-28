#![no_std]

/// Instruction selector trait.
use autosynth_ir::VCode;
use autosynth_regalloc::RegAlloc;

pub use autosynth_ir::CodeCtx;

/// Instruction selector — implemented per backend.
pub trait Selector {
    fn select(
        &mut self,
        regalloc: &mut RegAlloc,
        input: &mut CodeCtx,
    ) -> Result<CodeCtx, SelectorError>;
}

/// Errors during instruction selection.
#[derive(Debug)]
pub enum SelectorError {
    UnexpectedEnd,
    OperandUnderflow,
    Unhandled(VCode),
}
