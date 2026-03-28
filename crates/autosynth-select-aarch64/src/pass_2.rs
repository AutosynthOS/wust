use autosynth_ir::CompileError;
use autosynth_ir::{CodeCtx, Operand};
use autosynth_regalloc::RegAlloc;

pub fn resolve_pregs(regalloc: &mut RegAlloc, mut input: CodeCtx) -> Result<CodeCtx, CompileError> {
    for op in input.operands.iter_mut() {
        *op = regalloc.resolve_operand(*op)?;
    }
    Ok(input)
}
