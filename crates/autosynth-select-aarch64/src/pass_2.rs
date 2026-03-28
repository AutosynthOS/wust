use autosynth_ir::CompileError;
use autosynth_ir::{CodeCtx, Operand};
use autosynth_regalloc::RegAlloc;

pub fn resolve_pregs(regalloc: &mut RegAlloc, mut input: CodeCtx) -> Result<CodeCtx, CompileError> {
    for op in input.operands.iter_mut() {
        if let Operand::VReg(id) = op {
            *op = Operand::PReg(regalloc.resolve_vreg(*id)?);
        }
    }
    Ok(input)
}
