use wasmparser::ValType;

use crate::stack::Stack;
use crate::{Instance, Val, parse::func::FuncIdx};

mod exec_recursive;
pub(crate) use exec_recursive::Trap;

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

    // Wrap execution in the trap handler so that SIGSEGV from hitting
    // a guard page is caught and converted to Trap::StackOverflow.
    let guard_pages = stack.guard_page_ranges();
    let result = crate::trap_handler::enter_wasm(guard_pages, || {
        let mut fuel: i64 = i64::MAX;
        let mut depth: u32 = 0;
        exec_recursive::call_function(module, stack, func, &mut fuel, &mut depth)
    });

    match result {
        Ok(()) => {
            let results = read_results(stack, return_sp, &func.results);
            Ok(results)
        }
        Err(trap) => {
            stack.set_sp(return_sp);
            Err(trap.into())
        }
    }
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
