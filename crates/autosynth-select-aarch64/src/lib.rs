/// AArch64 instruction selector.
///
/// Works purely with VRegs — no PReg allocation. Folds constants
/// as immediates where possible, emits Materialize for the rest.
mod pass_1;

use autosynth_ir::{CodeCtx, CompileError};
use autosynth_regalloc::SharedVRegAllocator;
use autosynth_selector::Selector;

pub struct Aarch64Selector {
    pub alloc: SharedVRegAllocator,
}

impl Aarch64Selector {
    pub fn new(alloc: SharedVRegAllocator) -> Self {
        Self { alloc }
    }
}

impl Selector for Aarch64Selector {
    fn select(
        &mut self,
        input: &mut CodeCtx,
    ) -> Result<CodeCtx, CompileError> {
        pass_1::fold_immediates(&self.alloc, input)
    }
}
