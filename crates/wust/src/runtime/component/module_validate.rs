//! Module type constraint validation.
//!
//! Pure validation functions that check core module exports and imports
//! against declared type constraints. No dependency on instance state
//! beyond accessing exported module bytes.

use std::collections::HashMap;

use crate::runtime::module::{ExportKind, ImportKind, Module};

use super::instance::ComponentInstance;
use super::types::*;

/// Validate that core modules exported by an instance satisfy the declared
/// module type constraints.
///
/// For each module export that has a type constraint, parses the module bytes
/// and checks:
/// 1. All expected exports exist with the correct kind and type
/// 2. All expected imports exist with the correct kind and type
pub(super) fn validate_module_type_constraints(
    instance: &ComponentInstance,
    constraints: &HashMap<String, ModuleTypeConstraint>,
) -> Result<(), String> {
    for (export_name, constraint) in constraints {
        let Some(module_bytes) = instance.exported_modules.get(export_name) else {
            continue;
        };
        let module = Module::from_bytes(module_bytes)?;
        validate_module_exports(&module, &constraint.expected_exports, export_name)?;
        validate_module_imports(&module, &constraint.expected_imports)?;
    }
    Ok(())
}

/// Check that a module has all expected exports with matching kinds and types.
fn validate_module_exports(
    module: &Module,
    expected: &[ModuleItemConstraint],
    _module_export_name: &str,
) -> Result<(), String> {
    for expected_export in expected {
        let actual = module
            .exports
            .iter()
            .find(|e| e.name == expected_export.name);
        let Some(actual) = actual else {
            return Err(format!(
                "module export `{}` not defined",
                expected_export.name,
            ));
        };
        check_export_kind_matches(
            &actual.kind,
            &expected_export.item_type,
            &expected_export.name,
        )?;
        check_export_type_matches(module, actual, &expected_export.item_type)?;
    }
    Ok(())
}

/// Check that the kind of an export matches the expected item type.
///
/// Returns a descriptive error like "expected global found func" when the
/// kinds don't match.
fn check_export_kind_matches(
    actual_kind: &ExportKind,
    expected_type: &ModuleItemType,
    _name: &str,
) -> Result<(), String> {
    let kinds_match = matches!(
        (actual_kind, expected_type),
        (ExportKind::Func, ModuleItemType::Func { .. })
            | (ExportKind::Global, ModuleItemType::Global { .. })
            | (ExportKind::Memory, ModuleItemType::Memory { .. })
            | (ExportKind::Table, ModuleItemType::Table { .. })
    );
    if !kinds_match {
        let expected = module_item_type_kind_name(expected_type);
        let found = export_kind_name(actual_kind);
        return Err(format!("expected {} found {}", expected, found));
    }
    Ok(())
}

/// Check that the type of an export matches the expected type.
///
/// Assumes kinds already match. Returns an error like "export `f` has the
/// wrong type" when the detailed type (signature, val type, etc.) differs.
fn check_export_type_matches(
    module: &Module,
    actual: &crate::runtime::module::Export,
    expected_type: &ModuleItemType,
) -> Result<(), String> {
    match expected_type {
        ModuleItemType::Func { params, results } => {
            let type_idx = module.func_types.get(actual.index as usize);
            let actual_ft = type_idx.and_then(|&idx| module.types.get(idx as usize));
            if let Some(ft) = actual_ft {
                if ft.params() != params.as_slice() || ft.results() != results.as_slice() {
                    return Err(format!("export `{}` has the wrong type", actual.name,));
                }
            }
        }
        ModuleItemType::Global { ty, mutable } => {
            let global_local_idx = actual.index as usize;
            // Global index space: imports first, then module-defined globals.
            let num_global_imports = module.num_global_imports as usize;
            if global_local_idx < num_global_imports {
                // It's an imported global — find it in the imports.
                let mut global_count = 0usize;
                for import in &module.imports {
                    if let ImportKind::Global {
                        ty: actual_ty,
                        mutable: actual_mut,
                    } = &import.kind
                    {
                        if global_count == global_local_idx {
                            if actual_ty != ty || actual_mut != mutable {
                                return Err(
                                    format!("export `{}` has the wrong type", actual.name,),
                                );
                            }
                            break;
                        }
                        global_count += 1;
                    }
                }
            } else {
                let local_idx = global_local_idx - num_global_imports;
                if let Some(global_def) = module.globals.get(local_idx) {
                    if global_def.ty != *ty || global_def.mutable != *mutable {
                        return Err(format!("export `{}` has the wrong type", actual.name,));
                    }
                }
            }
        }
        ModuleItemType::Memory { min } => {
            if let Some(mem) = module.memories.get(actual.index as usize) {
                if mem.min < *min {
                    return Err(format!("export `{}` has the wrong type", actual.name,));
                }
            }
        }
        ModuleItemType::Table { min, element_type } => {
            if let Some(table) = module.tables.get(actual.index as usize) {
                if table.min < *min || table.element_type != *element_type {
                    return Err(format!("export `{}` has the wrong type", actual.name,));
                }
            }
        }
    }
    Ok(())
}

/// Check that every actual module import appears in the expected import list.
///
/// Module subtyping: a module's imports must be a subset of the declared
/// imports. An actual import not declared in the constraint is an error
/// ("module import `X::Y` not defined"). A constraint import that the module
/// doesn't actually have is fine (the host offered more than needed).
fn validate_module_imports(
    module: &Module,
    expected: &[ModuleImportConstraint],
) -> Result<(), String> {
    for actual in &module.imports {
        let matching_constraint = expected
            .iter()
            .find(|e| e.module == actual.module && e.name == actual.name);
        let Some(constraint) = matching_constraint else {
            return Err(format!(
                "module import `{}::{}` not defined",
                actual.module, actual.name,
            ));
        };
        check_import_kind_matches(
            &actual.kind,
            &constraint.item_type,
            &actual.module,
            &actual.name,
        )?;
        check_import_type_matches(module, actual, &constraint.item_type)?;
    }
    Ok(())
}

/// Check that the kind of a module import matches the expected item type.
fn check_import_kind_matches(
    actual_kind: &ImportKind,
    expected_type: &ModuleItemType,
    _module_name: &str,
    _import_name: &str,
) -> Result<(), String> {
    let kinds_match = matches!(
        (actual_kind, expected_type),
        (ImportKind::Func(_), ModuleItemType::Func { .. })
            | (ImportKind::Global { .. }, ModuleItemType::Global { .. })
            | (ImportKind::Memory(_), ModuleItemType::Memory { .. })
            | (ImportKind::Table(_), ModuleItemType::Table { .. })
    );
    if !kinds_match {
        let expected = import_kind_name(actual_kind);
        let found = module_item_type_kind_name(expected_type);
        return Err(format!("expected {} found {}", expected, found));
    }
    Ok(())
}

/// Check that the type of a module import matches the expected type.
fn check_import_type_matches(
    module: &Module,
    actual: &crate::runtime::module::Import,
    expected_type: &ModuleItemType,
) -> Result<(), String> {
    match (expected_type, &actual.kind) {
        (ModuleItemType::Func { params, results }, ImportKind::Func(type_idx)) => {
            if let Some(ft) = module.types.get(*type_idx as usize) {
                if ft.params() != params.as_slice() || ft.results() != results.as_slice() {
                    return Err(format!(
                        "module import `{}::{}` has the wrong type",
                        actual.module, actual.name,
                    ));
                }
            }
        }
        (
            ModuleItemType::Global { ty, mutable },
            ImportKind::Global {
                ty: actual_ty,
                mutable: actual_mut,
            },
        ) => {
            if actual_ty != ty || actual_mut != mutable {
                return Err(format!(
                    "module import `{}::{}` has the wrong type",
                    actual.module, actual.name,
                ));
            }
        }
        (ModuleItemType::Memory { min: offered_min }, ImportKind::Memory(actual_mem)) => {
            // Import subtyping: the constraint offers offered_min pages.
            // The module needs actual_mem.min pages. The constraint must
            // offer at least what the module needs.
            if *offered_min < actual_mem.min {
                return Err(format!(
                    "module import `{}::{}` has the wrong type",
                    actual.module, actual.name,
                ));
            }
        }
        (
            ModuleItemType::Table {
                min: offered_min,
                element_type,
            },
            ImportKind::Table(actual_table),
        ) => {
            // Import subtyping: the constraint must offer at least what
            // the module needs (min), and element types must match.
            if *offered_min < actual_table.min || actual_table.element_type != *element_type {
                return Err(format!(
                    "module import `{}::{}` has the wrong type",
                    actual.module, actual.name,
                ));
            }
        }
        _ => {}
    }
    Ok(())
}

/// Human-readable name for a module item type kind.
fn module_item_type_kind_name(item_type: &ModuleItemType) -> &'static str {
    match item_type {
        ModuleItemType::Func { .. } => "func",
        ModuleItemType::Global { .. } => "global",
        ModuleItemType::Memory { .. } => "memory",
        ModuleItemType::Table { .. } => "table",
    }
}

/// Human-readable name for an export kind.
fn export_kind_name(kind: &ExportKind) -> &'static str {
    match kind {
        ExportKind::Func => "func",
        ExportKind::Global => "global",
        ExportKind::Memory => "memory",
        ExportKind::Table => "table",
        ExportKind::Tag => "tag",
    }
}

/// Human-readable name for an import kind.
fn import_kind_name(kind: &ImportKind) -> &'static str {
    match kind {
        ImportKind::Func(_) => "func",
        ImportKind::Global { .. } => "global",
        ImportKind::Memory(_) => "memory",
        ImportKind::Table(_) => "table",
    }
}
