//! Public entry points for WASM execution.

use super::stack::Stack;
use crate::runtime::code::module::Module;
use crate::runtime::error::ExecError;
use crate::runtime::store::Store;
use crate::runtime::value::Value;

/// Invoke a WASM function by export name.
pub fn invoke(
    module: &Module,
    store: &mut Store,
    func_name: &str,
    args: &[Value],
) -> Result<Vec<Value>, ExecError> {
    let func_idx = module
        .export_func(func_name)
        .ok_or_else(|| ExecError::NotFound(format!("function '{func_name}' not exported")))?;
    call(module, store, func_idx, args)
}

/// Call a WASM function by index.
///
/// Creates a fresh mmap'd stack and runs the recursive interpreter.
/// Host function imports are called directly without entering
/// the interpreter.
pub fn call(
    module: &Module,
    store: &mut Store,
    func_idx: u32,
    args: &[Value],
) -> Result<Vec<Value>, ExecError> {
    if module.is_import(func_idx) {
        return if let Some(host_fn) = store.host_funcs.get(func_idx as usize) {
            host_fn(args, &mut store.memory).map_err(|e| ExecError::Trap(format!("trap: {e}")))
        } else {
            Err(ExecError::Trap(format!(
                "unresolved import function {func_idx}"
            )))
        };
    }

    let mut stack = Stack::new();
    super::exec::execute(&mut stack, module, store, func_idx, args)
}
