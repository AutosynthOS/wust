//! Host function trampolines for cross-instance and resource operations.
//!
//! Contains the trampoline factories that create `HostFunc` closures for
//! wiring imports between core instances, invoking child component exports,
//! and performing resource handle operations.

use std::rc::Rc;

use crate::runtime::canonical_abi;
use crate::runtime::exec;
use crate::runtime::store::{HostFunc, SharedStore};
use crate::runtime::value::Value;

use super::instance::{ComponentInstance, CoreExport, CoreInstance, ResolvedExport, ResourceEntry};
use super::types::*;

/// Create a host function trampoline that returns `result_count` zero values.
///
/// Used as a fallback when no source instance is available (e.g. for
/// unmatched imports).
pub(super) fn make_trampoline(result_count: usize) -> HostFunc {
    Box::new(move |_args, _mem| Ok(vec![Value::I32(0); result_count]))
}

/// Check if a synthetic instance export is a resource operation and return
/// the appropriate host function trampoline.
///
/// Returns `None` if the export is not a resource operation, in which case
/// the caller should fall back to a regular cross-instance trampoline.
pub(super) fn make_resource_trampoline(
    inst: &ComponentInstance,
    source_idx: usize,
    export_name: &str,
) -> Option<HostFunc> {
    let source = inst.core_instances.get(source_idx)?;
    let CoreInstance::Synthetic { exports } = source else {
        return None;
    };
    let core_export = exports.get(export_name)?;
    match core_export {
        CoreExport::ResourceNew { resource_type } => {
            let resource_type = *resource_type;
            let table = Rc::clone(&inst.resource_table);
            Some(Box::new(move |args: &[Value], _mem: &mut [u8]| {
                let rep = match args.first() {
                    Some(Value::I32(v)) => *v,
                    _ => 0,
                };
                let mut tbl = table.borrow_mut();
                let handle = tbl.len() as i32;
                tbl.push(Some(ResourceEntry { rep, resource_type }));
                Ok(vec![Value::I32(handle)])
            }))
        }
        CoreExport::ResourceRep { .. } => {
            let table = Rc::clone(&inst.resource_table);
            Some(Box::new(move |args: &[Value], _mem: &mut [u8]| {
                let handle = match args.first() {
                    Some(Value::I32(v)) => *v as usize,
                    _ => return Err("resource.rep: expected i32 handle".into()),
                };
                let tbl = table.borrow();
                match tbl.get(handle) {
                    Some(Some(entry)) => Ok(vec![Value::I32(entry.rep)]),
                    _ => Err(format!("resource.rep: invalid handle {handle}")),
                }
            }))
        }
        CoreExport::ResourceDrop { .. } => {
            let table = Rc::clone(&inst.resource_table);
            Some(Box::new(move |args: &[Value], _mem: &mut [u8]| {
                let handle = match args.first() {
                    Some(Value::I32(v)) => *v as usize,
                    _ => return Err("resource.drop: expected i32 handle".into()),
                };
                let mut tbl = table.borrow_mut();
                match tbl.get_mut(handle) {
                    Some(slot @ Some(_)) => {
                        *slot = None;
                        Ok(vec![])
                    }
                    _ => Err(format!("resource.drop: invalid handle {handle}")),
                }
            }))
        }
        _ => None,
    }
}

/// Create a host function that calls into a source core instance.
///
/// Captures the source instance's `Rc<Module>` and `SharedStore`, then
/// on each invocation borrows the store mutably and calls `exec::call`.
/// If the source is a synthetic instance, follows the `CoreExport::Func`
/// chain to the real instance.
pub(super) fn make_cross_instance_trampoline(
    inst: &ComponentInstance,
    source_idx: usize,
    export_name: &str,
    func_index: u32,
    result_count: usize,
) -> HostFunc {
    let source = &inst.core_instances[source_idx];
    match source {
        CoreInstance::Instantiated { module, store } => {
            let module = Rc::clone(module);
            let store = Rc::clone(store);
            Box::new(move |args, _mem| {
                let Ok(mut s) = store.try_borrow_mut() else {
                    return Ok(vec![Value::I32(0); result_count]);
                };
                match exec::call(&module, &mut s, func_index, args) {
                    Ok(values) => Ok(values),
                    Err(_) => Ok(vec![Value::I32(0); result_count]),
                }
            })
        }
        CoreInstance::Synthetic { exports } => {
            // Look up the specific export by name to handle synthetic
            // instances with multiple exports correctly.
            let export = exports.get(export_name);

            match export {
                Some(CoreExport::LoweredFunc {
                    child_index,
                    export_name,
                    string_encoding,
                }) => make_child_instance_trampoline(
                    inst,
                    *child_index,
                    export_name.clone(),
                    result_count,
                    *string_encoding,
                ),
                Some(CoreExport::LoweredCoreFunc { instance, index }) => {
                    make_lowered_core_trampoline(inst, *instance, *index, result_count)
                }
                Some(CoreExport::Func { instance, index }) => make_cross_instance_trampoline(
                    inst,
                    *instance,
                    export_name,
                    *index,
                    result_count,
                ),
                _ => {
                    // Fallback: try any matching export by kind.
                    let lowered = exports
                        .values()
                        .find(|e| matches!(e, CoreExport::LoweredFunc { .. }));
                    if let Some(CoreExport::LoweredFunc {
                        child_index,
                        export_name,
                        string_encoding,
                    }) = lowered
                    {
                        return make_child_instance_trampoline(
                            inst,
                            *child_index,
                            export_name.clone(),
                            result_count,
                            *string_encoding,
                        );
                    }
                    let lowered_core = exports
                        .values()
                        .find(|e| matches!(e, CoreExport::LoweredCoreFunc { .. }));
                    if let Some(CoreExport::LoweredCoreFunc { instance, index }) = lowered_core {
                        return make_lowered_core_trampoline(inst, *instance, *index, result_count);
                    }
                    let real = exports.values().find(
                        |e| matches!(e, CoreExport::Func { index, .. } if *index == func_index),
                    );
                    if let Some(CoreExport::Func { instance, index }) = real {
                        make_cross_instance_trampoline(
                            inst,
                            *instance,
                            export_name,
                            *index,
                            result_count,
                        )
                    } else {
                        make_trampoline(result_count)
                    }
                }
            }
        }
    }
}

/// Create a host function trampoline for a `canon lower` of `canon lift`.
///
/// Captures the component's `instantiating` flag and returns an error with
/// "cannot enter component instance" if the flag is set (i.e., the
/// component is still being instantiated). After instantiation completes,
/// the flag is cleared and subsequent calls proceed normally.
fn make_lowered_core_trampoline(
    inst: &ComponentInstance,
    source_instance: usize,
    func_index: u32,
    result_count: usize,
) -> HostFunc {
    let flag = Rc::clone(&inst.instantiating);
    let source = &inst.core_instances[source_instance];
    match source {
        CoreInstance::Instantiated { module, store } => {
            let module = Rc::clone(module);
            let store = Rc::clone(store);
            Box::new(move |args, _mem| {
                if flag.get() {
                    return Err("cannot enter component instance".into());
                }
                let Ok(mut s) = store.try_borrow_mut() else {
                    return Ok(vec![Value::I32(0); result_count]);
                };
                match exec::call(&module, &mut s, func_index, args) {
                    Ok(values) => Ok(values),
                    Err(_) => Ok(vec![Value::I32(0); result_count]),
                }
            })
        }
        CoreInstance::Synthetic { .. } => make_trampoline(result_count),
    }
}

/// Perform a fused adapter call using memory-based parameter passing.
///
/// When a component function has too many params to pass flat, `canon lower`
/// packs them into the caller's linear memory and passes `(argptr [, retptr])`.
/// This function:
/// 1. Reads param values from caller memory at argptr
/// 2. Calls callee's realloc to allocate in callee memory
/// 3. Writes params to callee memory
/// 4. Calls the core func with callee argptr
/// 5. Reads results from callee memory at returned retptr
/// 6. Writes results to caller memory at caller retptr
#[allow(clippy::too_many_arguments)]
fn fused_memory_transfer(
    args: &[Value],
    caller_mem: &mut [u8],
    param_types: &[ComponentResultType],
    result_type: ComponentResultType,
    module: &Rc<crate::runtime::module::Module>,
    store: &SharedStore,
    callee_mem_store: &Option<SharedStore>,
    func_idx: u32,
    callee_realloc_idx: Option<u32>,
    result_count: usize,
) -> Result<Vec<Value>, String> {
    let has_compound_result = matches!(result_type, ComponentResultType::Compound { .. });

    // Extract caller argptr (first arg) and optional retptr (last arg).
    let caller_argptr = match args.first() {
        Some(Value::I32(p)) => *p as u32,
        _ => return Err("expected i32 argptr in fused memory call".into()),
    };
    let caller_retptr = if has_compound_result && args.len() >= 2 {
        match args.last() {
            Some(Value::I32(p)) => Some(*p as u32),
            _ => None,
        }
    } else {
        None
    };

    // Step 1: Read param values from caller memory.
    let param_count = param_types.len();
    let param_values =
        canonical_abi::read_i32s_from_memory(caller_mem, caller_argptr, param_count)?;

    // Normalize params through lift-then-lower round-trip.
    let normalized = canonical_abi::normalize_args(&param_values, param_types)?;

    // Step 2: Allocate in callee memory via realloc.
    let callee_argptr = match callee_realloc_idx {
        Some(realloc_idx) => {
            let byte_size = (param_count as u32) * 4;
            canonical_abi::callee_realloc(module, store, realloc_idx, 4, byte_size)?
        }
        None => return Err("callee has no realloc for argptr-mode call".into()),
    };

    // Step 3: Write params to callee memory.
    {
        let mem_store = callee_mem_store.as_ref().unwrap_or(store);
        let mut s = mem_store.borrow_mut();
        canonical_abi::write_i32s_to_memory(&mut s.memory, callee_argptr, &normalized)?;
    }

    // Step 4: Call callee core func with callee argptr.
    let callee_args = vec![Value::I32(callee_argptr as i32)];
    let call_results = {
        let mut s = store.borrow_mut();
        exec::call(module, &mut s, func_idx, &callee_args).map_err(|e| format!("trap: {e}"))?
    };

    // Step 5: If compound result, read results from callee memory.
    if has_compound_result {
        let callee_retptr = match call_results.first() {
            Some(Value::I32(p)) => *p as u32,
            _ => return Err("callee did not return retptr for compound result".into()),
        };

        // Determine result count from the compound type.
        let result_values = {
            let mem_store = callee_mem_store.as_ref().unwrap_or(store);
            let s = mem_store.borrow();
            canonical_abi::read_i32s_from_memory(&s.memory, callee_retptr, result_count)?
        };

        // Step 6: Write results to caller memory at caller retptr.
        if let Some(retptr) = caller_retptr {
            canonical_abi::write_i32s_to_memory(caller_mem, retptr, &result_values)?;
            Ok(vec![])
        } else {
            Ok(result_values)
        }
    } else {
        // Scalar result: normalize and return directly.
        canonical_abi::normalize_result(&call_results, result_type)
    }
}

/// Create a host function trampoline that calls through to a child
/// component instance's exported function.
///
/// This handles `canon lower` of a function imported from a child
/// component instance. The trampoline invokes the child's function
/// and returns the results.
///
/// The trampoline validates:
/// - Caller retptr/argptr alignment for compound types
/// - Callee retptr alignment for compound result types
/// - String pointer alignment based on the caller's string encoding
/// - String content bounds in the caller's memory
fn make_child_instance_trampoline(
    inst: &ComponentInstance,
    child_index: usize,
    export_name: String,
    result_count: usize,
    caller_string_encoding: super::types::StringEncoding,
) -> HostFunc {
    // Resolve the child's export to find the actual core instance and func.
    let Some(child) = inst.child_instances.get(child_index) else {
        return make_trampoline(result_count);
    };
    let Some(resolved) = child.exports.get(&export_name) else {
        return make_trampoline(result_count);
    };
    match resolved {
        ResolvedExport::Local(func) => {
            let idx = func.core_instance_index;
            let func_idx = func.core_func_index;
            let param_types = func.param_types.clone();
            let result_type = func.result_type;
            let callee_realloc_idx = func.realloc_func_index;
            let callee_memory_instance = func.memory_instance;

            let Some(core_inst) = child.core_instances.get(idx) else {
                return make_trampoline(result_count);
            };

            // Capture callee's memory store if it differs from the func store.
            let callee_mem_store: Option<SharedStore> =
                callee_memory_instance.and_then(|mem_idx| {
                    if mem_idx == idx {
                        return None;
                    }
                    match child.core_instances.get(mem_idx)? {
                        CoreInstance::Instantiated { store, .. } => Some(Rc::clone(store)),
                        _ => None,
                    }
                });

            match core_inst {
                CoreInstance::Instantiated { module, store } => {
                    let module = Rc::clone(module);
                    let store = Rc::clone(store);
                    Box::new(move |args, caller_mem| {
                        let use_argptr =
                            canonical_abi::is_argptr_mode(args.len(), &param_types, result_type);
                        if use_argptr {
                            fused_memory_transfer(
                                args,
                                caller_mem,
                                &param_types,
                                result_type,
                                &module,
                                &store,
                                &callee_mem_store,
                                func_idx,
                                callee_realloc_idx,
                                result_count,
                            )
                        } else {
                            canonical_abi::validate_fused_args(
                                args,
                                &param_types,
                                result_type,
                                caller_mem,
                                caller_string_encoding,
                                callee_realloc_idx.is_some(),
                            )?;
                            canonical_abi::validate_callee_argptr(
                                &param_types,
                                callee_realloc_idx,
                                &module,
                                &store,
                            )?;
                            let normalized = canonical_abi::normalize_args(args, &param_types)?;
                            let Ok(mut s) = store.try_borrow_mut() else {
                                return Ok(vec![Value::I32(0); result_count]);
                            };
                            match exec::call(&module, &mut s, func_idx, &normalized) {
                                Ok(values) => {
                                    canonical_abi::validate_fused_results(&values, result_type)?;
                                    canonical_abi::normalize_result(&values, result_type)
                                }
                                Err(_) => Ok(vec![Value::I32(0); result_count]),
                            }
                        }
                    })
                }
                CoreInstance::Synthetic { .. } => make_trampoline(result_count),
            }
        }
        ResolvedExport::Child {
            child_index: grandchild_idx,
            export_name: inner_name,
        } => {
            // Delegate to grandchild.
            make_child_instance_trampoline(
                child,
                *grandchild_idx,
                inner_name.clone(),
                result_count,
                caller_string_encoding,
            )
        }
    }
}
