//! Core module instantiation and import resolution.
//!
//! Handles instantiating core modules within a component, resolving their
//! imports against arg instances, and wiring up func trampolines, globals,
//! and shared tables.

use std::cell::RefCell;
use std::rc::Rc;

use crate::runtime::exec;
use crate::runtime::module::{ExportKind, ImportKind, Module};
use crate::runtime::store::{HostFunc, SharedTable, Store};
use crate::runtime::value::Value;

use super::instance::{ComponentInstance, CoreExport, CoreInstance};
use super::trampoline::{make_cross_instance_trampoline, make_resource_trampoline, make_trampoline};
use super::types::*;

/// Instantiate a core module, wiring up imports from the arg instances.
///
/// For each import the module declares, we look up the matching arg
/// instance and find the corresponding export. Func imports become
/// host function trampolines that call back into the source instance.
/// Global imports are copied by value. Memory and table imports are
/// shared via Rc handles.
pub(super) fn instantiate_core_module(
    inst: &mut ComponentInstance,
    component: &ParsedComponent,
    module_index: u32,
    args: &[(String, CoreInstanceArg)],
) -> Result<(), String> {
    let module_bytes = component
        .core_modules
        .get(module_index as usize)
        .filter(|b| !b.is_empty())
        .ok_or_else(|| format!("module index {} out of bounds", module_index))?;
    let module = Rc::new(Module::from_bytes(module_bytes)?);

    let (host_funcs, imported_globals, imported_tables) = resolve_imports(&module, args, inst)?;
    let store = Store::new_with_imports(&module, host_funcs, imported_globals, imported_tables)?;
    let store = Rc::new(RefCell::new(store));

    if let Some(start_idx) = module.start {
        let mut s = store.borrow_mut();
        exec::call(&module, &mut s, start_idx, &[])
            .map_err(|e| format!("start function trap: {e}"))?;
    }

    inst.core_instances
        .push(CoreInstance::Instantiated { module, store });
    Ok(())
}

/// Resolve a module's imports against the provided arg instances.
///
/// Returns (host_funcs, imported_globals, imported_tables) suitable for
/// `Store::new_with_imports`.
fn resolve_imports(
    module: &Module,
    args: &[(String, CoreInstanceArg)],
    inst: &ComponentInstance,
) -> Result<(Vec<HostFunc>, Vec<Value>, Vec<SharedTable>), String> {
    let mut host_funcs: Vec<HostFunc> = Vec::new();
    let mut imported_globals: Vec<Value> = Vec::new();
    let mut imported_tables: Vec<SharedTable> = Vec::new();
    let mut func_import_idx: usize = 0;

    for import in &module.imports {
        let is_func = matches!(&import.kind, ImportKind::Func(_));
        resolve_single_import(
            import,
            args,
            inst,
            module,
            func_import_idx,
            &mut host_funcs,
            &mut imported_globals,
            &mut imported_tables,
        )?;
        if is_func {
            func_import_idx += 1;
        }
    }

    Ok((host_funcs, imported_globals, imported_tables))
}

/// Resolve one module import against the arg instances, appending to the
/// appropriate output vector.
///
/// If no arg matches the import's namespace, a default value is provided
/// (no-op trampoline for funcs, zero for globals). Otherwise, the export
/// is looked up in the source instance and wired in.
#[allow(clippy::too_many_arguments)]
fn resolve_single_import(
    import: &crate::runtime::module::Import,
    args: &[(String, CoreInstanceArg)],
    inst: &ComponentInstance,
    module: &Module,
    func_import_idx: usize,
    host_funcs: &mut Vec<HostFunc>,
    imported_globals: &mut Vec<Value>,
    imported_tables: &mut Vec<SharedTable>,
) -> Result<(), String> {
    let arg_instance_idx = find_arg_instance(args, &import.module);
    let result_count = func_result_count(module, func_import_idx);

    let Some(arg_idx) = arg_instance_idx else {
        provide_default_import(import, result_count, host_funcs, imported_globals);
        return Ok(());
    };

    let source = inst
        .core_instances
        .get(arg_idx)
        .ok_or_else(|| format!("arg instance {} out of bounds", arg_idx))?;

    let (export_kind, export_index) = source.resolve_export(&import.name).ok_or_else(|| {
        format!(
            "import '{}::{}' not found in instance {}",
            import.module, import.name, arg_idx
        )
    })?;

    match (&import.kind, &export_kind) {
        (ImportKind::Func(_), ExportKind::Func) => {
            if let Some(resource_func) = make_resource_trampoline(inst, arg_idx, &import.name) {
                host_funcs.push(resource_func);
            } else {
                host_funcs.push(make_cross_instance_trampoline(
                    inst, arg_idx, &import.name, export_index, result_count,
                ));
            }
        }
        (ImportKind::Global { .. }, ExportKind::Global) => {
            let val = get_global_value(inst, arg_idx, export_index)?;
            imported_globals.push(val);
        }
        // Memory imports are accepted but not yet wired up to share the
        // exporting instance's backing storage.
        (ImportKind::Memory(_), ExportKind::Memory) => {}
        (ImportKind::Table(_), ExportKind::Table) => {
            let shared_table = get_shared_table(inst, arg_idx, export_index)?;
            imported_tables.push(shared_table);
        }
        _ => {
            return Err(format!(
                "unsupported import kind for '{}::{}'",
                import.module, import.name
            ));
        }
    }
    Ok(())
}

/// Find the arg instance index that matches a given import namespace.
fn find_arg_instance(args: &[(String, CoreInstanceArg)], module_name: &str) -> Option<usize> {
    args.iter().find_map(|(name, arg)| {
        if name == module_name {
            match arg {
                CoreInstanceArg::Instance(idx) => Some(*idx as usize),
            }
        } else {
            None
        }
    })
}

/// Look up the number of results for a func import by its position in
/// the import list.
///
/// Falls back to 0 if the type cannot be resolved.
fn func_result_count(module: &Module, func_import_idx: usize) -> usize {
    module
        .func_types
        .get(func_import_idx)
        .and_then(|&type_idx| module.types.get(type_idx as usize))
        .map(|ft| ft.results().len())
        .unwrap_or(0)
}

/// Provide default values for an import that has no matching arg instance.
fn provide_default_import(
    import: &crate::runtime::module::Import,
    result_count: usize,
    host_funcs: &mut Vec<HostFunc>,
    imported_globals: &mut Vec<Value>,
) {
    match &import.kind {
        ImportKind::Func(_) => {
            host_funcs.push(make_trampoline(result_count));
        }
        ImportKind::Global { .. } => {
            imported_globals.push(Value::I32(0));
        }
        _ => {}
    }
}

/// Resolve through synthetic instance chains to find the real instantiated
/// store and resource index for a given core export kind.
///
/// Both globals and tables use the same pattern: for `Instantiated`
/// instances, the store is directly available; for `Synthetic` instances,
/// we follow the `CoreExport` chain until we reach a real instance.
///
/// `match_export` extracts the `(instance, index)` from a `CoreExport`
/// if it matches the desired kind (e.g. `Global` or `Table`).
fn resolve_core_resource<T>(
    inst: &ComponentInstance,
    instance_idx: usize,
    resource_idx: u32,
    kind_name: &str,
    match_export: fn(&CoreExport, u32) -> Option<(usize, u32)>,
    read_from_store: fn(&Store, u32) -> Option<T>,
) -> Result<T, String> {
    match inst.core_instances.get(instance_idx) {
        Some(CoreInstance::Instantiated { store, .. }) => {
            let store = store.borrow();
            read_from_store(&store, resource_idx)
                .ok_or_else(|| format!("{} {} out of bounds", kind_name, resource_idx))
        }
        Some(CoreInstance::Synthetic { exports }) => {
            let real = exports
                .values()
                .find_map(|e| match_export(e, resource_idx));
            match real {
                Some((real_instance, real_index)) => resolve_core_resource(
                    inst,
                    real_instance,
                    real_index,
                    kind_name,
                    match_export,
                    read_from_store,
                ),
                None => Err(format!(
                    "{} {} not found in synthetic instance {}",
                    kind_name, resource_idx, instance_idx,
                )),
            }
        }
        None => Err(format!("instance {} out of bounds", instance_idx)),
    }
}

/// Read a global value from a core instance.
///
/// For synthetic instances, follows the `CoreExport::Global` reference
/// to the real instantiated instance that holds the actual global value.
fn get_global_value(
    inst: &ComponentInstance,
    instance_idx: usize,
    global_idx: u32,
) -> Result<Value, String> {
    resolve_core_resource(
        inst,
        instance_idx,
        global_idx,
        "global",
        |export, idx| match export {
            CoreExport::Global { instance, index } if *index == idx => Some((*instance, *index)),
            _ => None,
        },
        |store, idx| store.globals.get(idx as usize).copied(),
    )
}

/// Get a shared table reference from a core instance.
///
/// For `Instantiated` instances, clones the `Rc` handle so the importing
/// module shares the same underlying table storage. For `Synthetic`
/// instances, follows the `CoreExport::Table` chain to the real instance.
fn get_shared_table(
    inst: &ComponentInstance,
    instance_idx: usize,
    table_idx: u32,
) -> Result<SharedTable, String> {
    resolve_core_resource(
        inst,
        instance_idx,
        table_idx,
        "table",
        |export, idx| match export {
            CoreExport::Table { instance, index } if *index == idx => Some((*instance, *index)),
            _ => None,
        },
        |store, idx| store.tables.get(idx as usize).cloned(),
    )
}
