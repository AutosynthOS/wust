/// AArch64 instruction selector.
mod pass_1;
mod pass_2;

use autosynth_ir::{CodeCtx, CompileError};
use autosynth_regalloc::RegAlloc;
use autosynth_selector::Selector;

pub struct Aarch64Selector;

impl Aarch64Selector {
    pub fn new() -> Self {
        Self
    }
}

impl Selector for Aarch64Selector {
    fn select(
        &mut self,
        regalloc: &mut RegAlloc,
        input: &mut CodeCtx,
    ) -> Result<CodeCtx, CompileError> {
        let mid = pass_1::fold_immediates(regalloc, input)?;
        pass_2::resolve_pregs(regalloc, mid)
    }
}
