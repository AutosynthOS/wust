//! PReg allocation pass — resolves VReg operands to PRegs.
//!
//! Backend-agnostic: walks the VCode stream, and for each
//! VReg operand, allocates a PReg via RegState.

use autosynth_ir::{CodeCtx, CompileError, VCode};
use autosynth_regalloc::RegState;
use autosynth_selector::Selector;

/// PReg allocation selector — resolves all VReg operands to PRegs.
pub struct PRegAllocSelector<'a> {
    state: &'a mut RegState,
}

impl<'a> PRegAllocSelector<'a> {
    pub fn new(state: &'a mut RegState) -> Self {
        Self { state }
    }
}

impl Selector for PRegAllocSelector<'_> {
    fn select(&mut self, input: &mut CodeCtx) -> Result<CodeCtx, CompileError> {
        let mut output = CodeCtx::new();
        while let Some(item) = input.next() {
            match item {
                VCode::Operand(op) => {
                    let resolved = self.state.resolve_operand(op)?;
                    output.push_operand(resolved);
                }
                other => output.push(other),
            }
        }
        Ok(output)
    }
}
