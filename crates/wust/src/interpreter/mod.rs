use wasmparser::ValType;

use crate::stack::Stack;
use crate::{Instance, Val, parse::func::FuncIdx};

mod exec;

pub(crate) fn call(
    instance: &mut Instance,
    func_idx: FuncIdx,
    args: &[Val],
) -> Result<Vec<Val>, anyhow::Error> {
    let Instance { module, stack } = instance;

    let func = module
        .get_func(func_idx)
        .ok_or_else(|| anyhow::anyhow!("function {func_idx:?} not found"))?;

    for arg in args {
        stack.push_val(arg);
    }

    exec::execute(func, stack)?;

    // Pop result values off the stack (in reverse, then reverse back).
    let results = pop_results(stack, &func.results);

    Ok(results)
}

/// Pop `result_types.len()` values from the stack, returning them in order.
///
/// Results are on top of the stack in order (first result deepest),
/// so we pop in reverse then flip.
fn pop_results(stack: &mut Stack, result_types: &[ValType]) -> Vec<Val> {
    let mut results: Vec<Val> = result_types
        .iter()
        .rev()
        .map(|ty| pop_typed(stack, ty))
        .collect();
    results.reverse();
    results
}

/// Pop a single value from the stack, interpreting the raw u64 bits
/// according to the given ValType.
fn pop_typed(stack: &mut Stack, ty: &ValType) -> Val {
    match ty {
        ValType::I32 => Val::I32(stack.pop_i32()),
        ValType::I64 => Val::I64(stack.pop_i64()),
        ValType::F32 => Val::F32(stack.pop_f32()),
        ValType::F64 => Val::F64(stack.pop_f64()),
        ValType::V128 => {
            let hi = stack.pop_u64();
            let lo = stack.pop_u64();
            Val::V128((hi as u128) << 64 | lo as u128)
        }
        ValType::Ref(ref_ty) => {
            stack.pop_u64();
            Val::Ref(*ref_ty)
        }
    }
}
