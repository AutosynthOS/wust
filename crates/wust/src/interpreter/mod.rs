use wasmparser::ValType;

use crate::stack::Stack;
use crate::{Instance, Val, parse::func::FuncIdx};

mod exec_recursive;
mod exec_stack;

pub(crate) fn call(
    instance: &mut Instance,
    func_idx: FuncIdx,
    args: &[Val],
) -> Result<Vec<Val>, anyhow::Error> {
    let Instance { module, stack } = instance;

    let func = module
        .get_func(func_idx)
        .ok_or_else(|| anyhow::anyhow!("function {func_idx:?} not found"))?;

    let return_sp = stack.sp();

    // Push args onto the operand stack.
    for arg in args {
        stack.push_val(arg);
    }

    // call_function expects args already on stack.
    let mut fuel: i64 = i64::MAX;
    exec_recursive::call_function(module, stack, func, &mut fuel)?;

    // Results are now at return_sp.
    let results = read_results(stack, return_sp, &func.results);

    Ok(results)
}

/// Read result values starting at `base` offset, using type info to
/// interpret the raw u64 bits.
fn read_results(stack: &Stack, base: usize, result_types: &[ValType]) -> Vec<Val> {
    result_types
        .iter()
        .enumerate()
        .map(|(i, ty)| read_typed(stack, base + i * 8, ty))
        .collect()
}

/// Read a single value at a byte offset, interpreting raw bits by ValType.
fn read_typed(stack: &Stack, offset: usize, ty: &ValType) -> Val {
    let raw = stack.read_u64_at(offset);
    match ty {
        ValType::I32 => Val::I32(raw as i32),
        ValType::I64 => Val::I64(raw as i64),
        ValType::F32 => Val::F32(f32::from_bits(raw as u32)),
        ValType::F64 => Val::F64(f64::from_bits(raw)),
        ValType::V128 => {
            let lo = raw as u128;
            let hi = stack.read_u64_at(offset + 8) as u128;
            Val::V128(hi << 64 | lo)
        }
        ValType::Ref(ref_ty) => Val::Ref(*ref_ty),
    }
}
