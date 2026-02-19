//! Named import registry for component instantiation.
//!
//! The [`Linker`] collects named imports (instances and functions) and
//! resolves them against a component's declared imports during
//! instantiation.

use std::collections::HashMap;

use crate::component::Component;
use crate::parse::types::{ComponentFuncDef, ComponentImportKind, ParsedComponent};
use crate::runtime::component::instance::ComponentInstance;

/// Entry in the linker registry.
struct LinkerEntry {
    kind: ComponentImportKind,
    instance: ComponentInstance,
}

/// A named import registry that resolves component imports during
/// instantiation.
///
/// Register named instances and functions, then call
/// [`Linker::instantiate`] to resolve a component's imports and produce
/// a live [`ComponentInstance`].
///
/// # Examples
///
/// ```ignore
/// let mut linker = Linker::new();
/// linker.instance("host", host_instance);
/// let instance = linker.instantiate(&component)?;
/// ```
pub struct Linker {
    entries: HashMap<String, LinkerEntry>,
}

impl Linker {
    /// Create an empty linker.
    pub fn new() -> Self {
        Linker {
            entries: HashMap::new(),
        }
    }

    /// Register a named instance import.
    pub fn instance(&mut self, name: &str, inst: ComponentInstance) {
        self.entries.insert(
            name.to_string(),
            LinkerEntry {
                kind: ComponentImportKind::Instance,
                instance: inst,
            },
        );
    }

    /// Register a named function import.
    pub fn func(&mut self, name: &str, inst: ComponentInstance) {
        self.entries.insert(
            name.to_string(),
            LinkerEntry {
                kind: ComponentImportKind::Func,
                instance: inst,
            },
        );
    }

    /// Check whether an import name is already registered.
    pub fn has(&self, name: &str) -> bool {
        self.entries.contains_key(name)
    }

    /// Resolve a component's imports and instantiate it.
    ///
    /// For each import declared by the component:
    /// 1. Look up the name in the registry.
    /// 2. Verify the registered kind matches the import kind.
    /// 3. For instance imports: validate required exports and module type
    ///    constraints, then collect into positional import list.
    /// 4. For func imports: find the placeholder slot and record a patch.
    /// 5. Apply func patches (if any) by rewriting the component AST.
    /// 6. Resolve and instantiate.
    ///
    /// Returns an error if any import is missing or has a kind mismatch.
    pub fn instantiate(&self, component: &Component) -> Result<ComponentInstance, String> {
        let types = &component.types;
        let features = component.features;
        let component = &component.parsed;
        let mut import_instances = Vec::new();
        let mut func_patches: Vec<(usize, String, ComponentInstance)> = Vec::new();

        for import_def in component.imports() {
            let Some(entry) = self.entries.get(&import_def.name) else {
                return Err(format!("import '{}' was not found", import_def.name));
            };
            if import_def.kind != entry.kind {
                return Err(
                    format!("expected {:?} found {:?}", import_def.kind, entry.kind).to_lowercase(),
                );
            }
            match import_def.kind {
                ComponentImportKind::Instance => {
                    let instance = entry.instance.export_view();
                    validate_required_exports(
                        &instance,
                        &import_def.name,
                        &import_def.required_exports,
                    )?;
                    import_instances.push(instance);
                }
                ComponentImportKind::Func => {
                    let host_inst = entry.instance.export_view();
                    if let Some(slot_idx) =
                        find_func_import_slot(&component.component_funcs, &import_def.name)
                    {
                        func_patches.push((slot_idx, import_def.name.clone(), host_inst));
                    }
                }
                _ => {}
            }
        }

        if func_patches.is_empty() {
            ComponentInstance::instantiate_with_imports(component, import_instances, types, features)
        } else {
            let shift = func_patches.len() as u32;
            let mut patched = component.clone();
            let mut patched_slots = Vec::new();
            for (slot_idx, name, host_inst) in func_patches {
                let child_idx = import_instances.len() as u32;
                patched.component_funcs[slot_idx] = ComponentFuncDef::AliasInstanceExport {
                    instance_index: child_idx,
                    name,
                };
                import_instances.push(host_inst);
                patched_slots.push(slot_idx);
            }
            shift_component_instance_indices(&mut patched, shift, &patched_slots);
            ComponentInstance::instantiate_with_imports(&patched, import_instances, types, features)
        }
    }
}

/// Check that an instance provides all required exports.
fn validate_required_exports(
    instance: &ComponentInstance,
    import_name: &str,
    required_exports: &[String],
) -> Result<(), String> {
    for required in required_exports {
        if !instance.has_export(required) {
            return Err(format!(
                "import '{}': required export '{}' was not found",
                import_name, required,
            ));
        }
    }
    Ok(())
}

/// Find the component_funcs slot for a func import placeholder.
fn find_func_import_slot(funcs: &[ComponentFuncDef], name: &str) -> Option<usize> {
    funcs.iter().position(|f| {
        matches!(f, ComponentFuncDef::AliasInstanceExport {
            instance_index, name: n
        } if *instance_index == u32::MAX && n == name)
    })
}

/// Shift all component instance index references in a component by `shift`.
fn shift_component_instance_indices(component: &mut ParsedComponent, shift: u32, skip: &[usize]) {
    component.instance_import_count += shift;
    for (i, func) in component.component_funcs.iter_mut().enumerate() {
        if skip.contains(&i) {
            continue;
        }
        if let ComponentFuncDef::AliasInstanceExport { instance_index, .. } = func {
            if *instance_index != u32::MAX {
                *instance_index += shift;
            }
        }
    }
    let mut new_aliased_modules = HashMap::new();
    for (k, (inst_idx, name)) in &component.aliased_core_modules {
        new_aliased_modules.insert(*k, (*inst_idx + shift, name.clone()));
    }
    component.aliased_core_modules = new_aliased_modules;
    let mut new_aliased_components = HashMap::new();
    for (k, (inst_idx, name)) in &component.aliased_inner_components {
        new_aliased_components.insert(*k, (*inst_idx + shift, name.clone()));
    }
    component.aliased_inner_components = new_aliased_components;
}
