//! Alias and export resolution for component instances.
//!
//! Contains the logic for:
//! - Building synthetic core instances from explicit exports
//! - Resolving core index-space aliases to live `CoreExport` values
//! - Resolving component-level exports to `ResolvedExport` entries

use std::collections::HashMap;

use super::instance::{
    make_core_export, CoreExport, CoreInstance, ResolvedExport, ResolvedFunc,
};
use super::types::*;
use crate::runtime::module::ExportKind;

// ---------------------------------------------------------------------------
// Synthetic instance construction
// ---------------------------------------------------------------------------

/// Build a synthetic core instance from explicit exports.
///
/// Each `CoreInstanceExportDef` references an item in the component's core
/// index space (funcs, globals, memories, tables). We look up the alias
/// definition to find which instance and export name it came from, then
/// resolve that against the live instances to produce a `CoreExport`.
pub(super) fn build_synthetic_instance(
    core_instances: &[CoreInstance],
    component: &Component,
    export_defs: &[CoreInstanceExportDef],
) -> Result<CoreInstance, String> {
    let mut exports = HashMap::new();

    for def in export_defs {
        let core_export =
            resolve_alias_to_core_export(core_instances, component, def.kind, def.index)?;
        exports.insert(def.name.clone(), core_export);
    }

    Ok(CoreInstance::Synthetic { exports })
}

/// Look up an alias def by index in a slice, returning its coordinates.
///
/// Returns `(instance_index, name)` or a descriptive error if the index is
/// out of bounds.
fn get_alias_coords<'a>(
    aliases: &'a [CoreAliasDef],
    index: u32,
    label: &str,
) -> Result<(u32, &'a str), String> {
    let alias = aliases
        .get(index as usize)
        .ok_or_else(|| format!("core {} alias index {} out of bounds", label, index))?;
    Ok((alias.instance_index, &alias.name))
}

/// Resolve an alias reference (kind + index in the component's core index
/// space) to a live `CoreExport`.
///
/// For `Func` kind, the core func may be an alias (resolved via a core
/// instance export) or an intrinsic (canon lower, resource ops, async
/// builtins) which resolves to a no-op trampoline.
fn resolve_alias_to_core_export(
    core_instances: &[CoreInstance],
    component: &Component,
    kind: wasmparser::ExternalKind,
    index: u32,
) -> Result<CoreExport, String> {
    if kind == wasmparser::ExternalKind::Func {
        return resolve_core_func_def_to_export(core_instances, component, index);
    }
    let (instance_index, name) = match kind {
        wasmparser::ExternalKind::Global => {
            get_alias_coords(&component.core_globals, index, "global")?
        }
        wasmparser::ExternalKind::Memory => {
            get_alias_coords(&component.core_memories, index, "memory")?
        }
        wasmparser::ExternalKind::Table => {
            get_alias_coords(&component.core_tables, index, "table")?
        }
        wasmparser::ExternalKind::Tag => {
            get_alias_coords(&component.core_tags, index, "tag")?
        }
        _ => return Err("unsupported export kind in synthetic instance".to_string()),
    };
    resolve_aliased_export(core_instances, instance_index, name, kind)
}

/// Resolve a core func def to a `CoreExport`.
///
/// For `AliasInstanceExport`, looks up the export in the referenced core
/// instance. For `Lower` wrapping a `Lift`, follows the chain to the
/// underlying core func. For resource ops and async builtins, returns
/// a `CoreExport::Trampoline`.
fn resolve_core_func_def_to_export(
    core_instances: &[CoreInstance],
    component: &Component,
    index: u32,
) -> Result<CoreExport, String> {
    let func_def = component
        .core_funcs
        .get(index as usize)
        .ok_or_else(|| format!("core func index {} out of bounds", index))?;
    match func_def {
        CoreFuncDef::AliasInstanceExport { instance_index, name } => {
            resolve_aliased_export(
                core_instances,
                *instance_index,
                name,
                wasmparser::ExternalKind::Func,
            )
        }
        CoreFuncDef::Lower { func_index } => {
            // canon lower wraps a component func. If the component func is
            // a Lift over a core func, resolve to a LoweredCoreFunc that
            // will trap during instantiation (re-entrance check).
            // If it's an alias to a child instance export, produce a
            // LoweredFunc that calls through to the child.
            let comp_func = component.component_funcs.get(*func_index as usize);
            match comp_func {
                Some(ComponentFuncDef::Lift { core_func_index, .. }) => {
                    let inner = resolve_core_func_def_to_export(
                        core_instances, component, *core_func_index,
                    )?;
                    match inner {
                        CoreExport::Func { instance, index } => {
                            Ok(CoreExport::LoweredCoreFunc { instance, index })
                        }
                        other => Ok(other),
                    }
                }
                Some(ComponentFuncDef::AliasInstanceExport {
                    instance_index,
                    name,
                }) => Ok(CoreExport::LoweredFunc {
                    child_index: *instance_index as usize,
                    export_name: name.clone(),
                }),
                _ => Ok(CoreExport::Trampoline),
            }
        }
        _ => Ok(CoreExport::Trampoline),
    }
}

/// Look up a core export by instance index and name, returning a
/// descriptive error on failure.
fn resolve_aliased_export(
    core_instances: &[CoreInstance],
    instance_index: u32,
    name: &str,
    kind: wasmparser::ExternalKind,
) -> Result<CoreExport, String> {
    let label = match kind {
        wasmparser::ExternalKind::Func => "func",
        wasmparser::ExternalKind::Global => "global",
        wasmparser::ExternalKind::Memory => "memory",
        wasmparser::ExternalKind::Table => "table",
        wasmparser::ExternalKind::Tag => "tag",
        _ => "unknown",
    };
    let inst_idx = instance_index as usize;
    let instance = core_instances
        .get(inst_idx)
        .ok_or_else(|| format!("{} instance {} out of bounds", label, instance_index))?;
    match instance {
        CoreInstance::Instantiated { module, .. } => module
            .exports
            .iter()
            .find(|e| e.name == name)
            .map(|e| make_core_export(&e.kind, inst_idx, e.index))
            .ok_or_else(|| {
                format!(
                    "{} export '{}' not found in instance {}",
                    label, name, instance_index
                )
            }),
        CoreInstance::Synthetic { exports } => exports.get(name).cloned().ok_or_else(|| {
            format!(
                "{} export '{}' not found in instance {}",
                label, name, instance_index
            )
        }),
    }
}

// ---------------------------------------------------------------------------
// Component export resolution
// ---------------------------------------------------------------------------

/// Resolve component-level exports by following the chain:
/// component export → component func → core func alias → core instance export.
pub(super) fn resolve_component_exports(
    core_instances: &[CoreInstance],
    component: &Component,
) -> Result<HashMap<String, ResolvedExport>, String> {
    let mut exports = HashMap::new();
    for export_def in &component.exports {
        if export_def.kind != ComponentExternalKind::Func {
            continue;
        }
        resolve_single_export(&mut exports, core_instances, component, export_def)?;
    }
    Ok(exports)
}

/// Resolve one component-level func export into the exports map.
///
/// For `Lift` funcs, follows the chain: canon lift → core func alias →
/// core instance export. For `AliasInstanceExport` funcs, delegates to
/// a child component instance.
fn resolve_single_export(
    exports: &mut HashMap<String, ResolvedExport>,
    core_instances: &[CoreInstance],
    component: &Component,
    export_def: &ComponentExportDef,
) -> Result<(), String> {
    let comp_func = component
        .component_funcs
        .get(export_def.index as usize)
        .ok_or_else(|| format!("component func index {} out of bounds", export_def.index))?;

    match comp_func {
        ComponentFuncDef::Lift {
            core_func_index,
            type_index,
            memory_index,
            realloc_func_index,
        } => {
            let core_func = component
                .core_funcs
                .get(*core_func_index as usize)
                .ok_or_else(|| {
                    format!("core func index {} out of bounds", core_func_index)
                })?;
            let param_types = lookup_param_types(component, *type_index);
            let result_type = lookup_result_type(component, *type_index);
            let resolved = resolve_core_func_to_resolved(
                core_instances,
                component,
                core_func,
                param_types,
                result_type,
                *memory_index,
                *realloc_func_index,
            )?;
            exports.insert(export_def.name.clone(), ResolvedExport::Local(resolved));
        }
        ComponentFuncDef::AliasInstanceExport {
            instance_index,
            name,
        } => {
            let child_idx = *instance_index as usize;
            exports.insert(
                export_def.name.clone(),
                ResolvedExport::Child {
                    child_index: child_idx,
                    export_name: name.clone(),
                },
            );
        }
    }
    Ok(())
}

/// Follow a core func definition to its live instance, returning a
/// `ResolvedFunc`.
///
/// For `AliasInstanceExport` variants, this resolves the alias chain
/// through the core instance's export map. For `Lower`, `ResourceNew`,
/// `ResourceRep`, `ResourceDrop`, and `AsyncBuiltin`, these are currently
/// unsupported and return an error.
pub(super) fn resolve_core_func_to_resolved(
    core_instances: &[CoreInstance],
    component: &Component,
    core_func: &CoreFuncDef,
    param_types: Vec<ComponentResultType>,
    result_type: ComponentResultType,
    memory_index: Option<u32>,
    realloc_func_index: Option<u32>,
) -> Result<ResolvedFunc, String> {
    match core_func {
        CoreFuncDef::AliasInstanceExport {
            instance_index,
            name,
        } => {
            let memory_instance =
                resolve_memory_instance(core_instances, component, memory_index)?;
            let inst_idx = *instance_index as usize;
            let instance = core_instances
                .get(inst_idx)
                .ok_or_else(|| format!("core instance {} out of bounds", instance_index))?;
            match instance {
                CoreInstance::Instantiated { module, .. } => {
                    let export = module
                        .exports
                        .iter()
                        .find(|e| e.name == *name)
                        .ok_or_else(|| format!("core export '{}' not found", name))?;
                    match &export.kind {
                        ExportKind::Func => Ok(ResolvedFunc {
                            core_instance_index: inst_idx,
                            core_func_index: export.index,
                            param_types: param_types.clone(),
                            result_type,
                            memory_instance,
                            realloc_func_index,
                        }),
                        _ => Err(format!("core export '{}' is not a func", name)),
                    }
                }
                CoreInstance::Synthetic { exports } => match exports.get(name.as_str()) {
                    Some(CoreExport::Func { instance, index }) => Ok(ResolvedFunc {
                        core_instance_index: *instance,
                        core_func_index: *index,
                        param_types: param_types.clone(),
                        result_type,
                        memory_instance,
                        realloc_func_index,
                    }),
                    _ => Err(format!("core export '{}' not found or not a func", name)),
                },
            }
        }
        CoreFuncDef::Lower { func_index } => {
            // canon lower wraps a component func as a core func.
            // If the component func is an alias to a child instance export,
            // delegate there. Otherwise, resolve via the first available core
            // instance as a trampoline.
            let comp_func = component
                .component_funcs
                .get(*func_index as usize);
            match comp_func {
                Some(ComponentFuncDef::AliasInstanceExport { .. }) => {
                    // Lowering an aliased component func → use a dummy
                    // resolved func since the actual import is not available.
                    Ok(ResolvedFunc {
                        core_instance_index: 0,
                        core_func_index: 0,
                        param_types,
                        result_type,
                        memory_instance: None,
                        realloc_func_index: None,
                    })
                }
                Some(ComponentFuncDef::Lift { core_func_index, type_index, memory_index: mem_idx, realloc_func_index: realloc_idx }) => {
                    // Lowering a lifted func → the underlying core func.
                    let inner_core_func = component
                        .core_funcs
                        .get(*core_func_index as usize)
                        .ok_or_else(|| format!("core func index {} out of bounds", core_func_index))?;
                    let inner_params = lookup_param_types(component, *type_index);
                    let inner_result = lookup_result_type(component, *type_index);
                    resolve_core_func_to_resolved(
                        core_instances, component, inner_core_func,
                        inner_params, inner_result, *mem_idx, *realloc_idx,
                    )
                }
                None => {
                    Err(format!("component func index {} out of bounds", func_index))
                }
            }
        }
        // Resource operations and async builtins resolve to a dummy
        // trampoline — the core func slot is occupied but the operation
        // is not yet implemented, so calls return default zero values.
        CoreFuncDef::ResourceNew { .. }
        | CoreFuncDef::ResourceRep { .. }
        | CoreFuncDef::ResourceDrop { .. }
        | CoreFuncDef::AsyncBuiltin => Ok(ResolvedFunc {
            core_instance_index: 0,
            core_func_index: 0,
            param_types,
            result_type,
            memory_instance: None,
            realloc_func_index: None,
        }),
    }
}

/// Resolve a component-level core memory index to the core instance that
/// owns the memory.
///
/// Returns `None` if `memory_index` is `None` (no memory option on canon lift).
fn resolve_memory_instance(
    core_instances: &[CoreInstance],
    component: &Component,
    memory_index: Option<u32>,
) -> Result<Option<usize>, String> {
    let Some(idx) = memory_index else {
        return Ok(None);
    };
    let mem_def = component
        .core_memories
        .get(idx as usize)
        .ok_or_else(|| format!("core memory index {} out of bounds", idx))?;
    let core_inst_idx = mem_def.instance_index as usize;
    match core_instances.get(core_inst_idx) {
        Some(CoreInstance::Instantiated { .. }) => Ok(Some(core_inst_idx)),
        Some(CoreInstance::Synthetic { .. }) => {
            Err("memory cannot be on a synthetic instance".into())
        }
        None => Err(format!("memory instance {} out of bounds", core_inst_idx)),
    }
}

/// Look up the result type from a component func type index.
pub(super) fn lookup_result_type(
    component: &Component,
    type_index: u32,
) -> ComponentResultType {
    component
        .component_types
        .get(type_index as usize)
        .and_then(|t| t.as_ref())
        .map(|t| t.result)
        .unwrap_or(ComponentResultType::Unknown)
}

/// Look up the param types from a component func type index.
pub(super) fn lookup_param_types(
    component: &Component,
    type_index: u32,
) -> Vec<ComponentResultType> {
    component
        .component_types
        .get(type_index as usize)
        .and_then(|t| t.as_ref())
        .map(|t| t.params.clone())
        .unwrap_or_default()
}
