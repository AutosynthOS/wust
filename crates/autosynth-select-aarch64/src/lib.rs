/// AArch64 instruction selector.
///
/// Pass 1: commutative swap — move consts to rhs.
/// Pass 2: fold immediates — fold rhs consts as UImm12.
mod pass_1;
mod pass_2;

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
        let mut swapped = pass_1::commutative_swap(&self.alloc, input)?;
        pass_2::fold_immediates(&self.alloc, &mut swapped)
    }
}
