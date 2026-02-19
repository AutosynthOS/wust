//! Component binary section parsing.
//!
//! Extracts component sections from raw bytes into our parsed types.

use super::types::*;

// ---------------------------------------------------------------------------
// Section parsing
// ---------------------------------------------------------------------------

/// Walk all payloads in a component binary and dispatch each recognized
/// section to the appropriate parser.
///
/// Only processes sections at depth 1 (root-level). Inner component
/// sections are ignored — they belong to nested components and must not
/// leak into the outer component's index spaces.
pub(crate) fn parse_component_sections(
    component: &mut ParsedComponent,
    bytes: &[u8],
) -> Result<(), String> {
    let parser = wasmparser::Parser::new(0);
    let mut depth: u32 = 0;
    for payload in parser.parse_all(bytes) {
        let payload = payload.map_err(|e| format!("parse error: {e}"))?;
        match payload {
            wasmparser::Payload::Version { .. } => {
                depth += 1;
                continue;
            }
            wasmparser::Payload::End(_) => {
                depth -= 1;
                continue;
            }
            _ => {}
        }
        if depth != 1 {
            continue;
        }
        match payload {
            wasmparser::Payload::ModuleSection {
                unchecked_range, ..
            } => {
                component.core_modules.push(bytes[unchecked_range].to_vec());
            }
            wasmparser::Payload::InstanceSection(reader) => {
                parse_instance_section(component, reader)?;
            }
            wasmparser::Payload::ComponentAliasSection(reader) => {
                parse_alias_section(component, reader)?;
            }
            wasmparser::Payload::ComponentCanonicalSection(reader) => {
                parse_canonical_section(component, reader)?;
            }
            wasmparser::Payload::ComponentExportSection(reader) => {
                parse_export_section(component, reader)?;
            }
            wasmparser::Payload::ComponentTypeSection(reader) => {
                parse_type_section(component, reader)?;
            }
            wasmparser::Payload::ComponentSection {
                unchecked_range, ..
            } => {
                component
                    .inner_components
                    .push(bytes[unchecked_range].to_vec());
            }
            wasmparser::Payload::ComponentInstanceSection(reader) => {
                parse_component_instance_section(component, reader)?;
            }
            wasmparser::Payload::ComponentImportSection(reader) => {
                parse_component_import_section(component, reader)?;
            }
            _ => {}
        }
    }
    Ok(())
}

fn parse_instance_section(
    component: &mut ParsedComponent,
    reader: wasmparser::InstanceSectionReader,
) -> Result<(), String> {
    for instance in reader {
        let instance = instance.map_err(|e| format!("instance parse error: {e}"))?;
        match instance {
            wasmparser::Instance::Instantiate { module_index, args } => {
                let args = args
                    .iter()
                    .map(|a| (a.name.to_string(), CoreInstanceArg::Instance(a.index)))
                    .collect();
                component
                    .core_instances
                    .push(CoreInstanceDef::Instantiate { module_index, args });
            }
            wasmparser::Instance::FromExports(exports) => {
                let defs = exports
                    .iter()
                    .map(|e| CoreInstanceExportDef {
                        name: e.name.to_string(),
                        kind: e.kind,
                        index: e.index,
                    })
                    .collect();
                component
                    .core_instances
                    .push(CoreInstanceDef::FromExports(defs));
            }
        }
    }
    Ok(())
}

fn parse_alias_section(
    component: &mut ParsedComponent,
    reader: wasmparser::ComponentAliasSectionReader,
) -> Result<(), String> {
    for alias in reader {
        let alias = alias.map_err(|e| format!("alias parse error: {e}"))?;
        match alias {
            wasmparser::ComponentAlias::CoreInstanceExport {
                instance_index,
                kind,
                name,
            } => {
                register_core_instance_export(component, instance_index, kind, name.to_string());
            }
            wasmparser::ComponentAlias::InstanceExport {
                kind,
                instance_index,
                name,
            } => {
                register_component_instance_export(
                    component,
                    instance_index,
                    kind,
                    name.to_string(),
                );
            }
            wasmparser::ComponentAlias::Outer { kind, count, index } => {
                register_outer_alias(component, kind, count, index);
            }
        }
    }
    Ok(())
}

/// Record an outer alias and insert a placeholder in the appropriate
/// index space.
///
/// The placeholder is filled in later when the parent context is
/// available during instantiation.
fn register_outer_alias(
    component: &mut ParsedComponent,
    kind: wasmparser::ComponentOuterAliasKind,
    count: u32,
    index: u32,
) {
    let (alias_kind, placeholder_index) = match kind {
        wasmparser::ComponentOuterAliasKind::CoreModule => {
            let idx = component.core_modules.len() as u32;
            component.core_modules.push(Vec::new());
            (OuterAliasKind::CoreModule, idx)
        }
        wasmparser::ComponentOuterAliasKind::Component => {
            let idx = component.inner_components.len() as u32;
            component.inner_components.push(Vec::new());
            (OuterAliasKind::Component, idx)
        }
        wasmparser::ComponentOuterAliasKind::CoreType => (OuterAliasKind::CoreType, 0),
        wasmparser::ComponentOuterAliasKind::Type => {
            let idx = component.component_types.len() as u32;
            component.component_types.push(None);
            (OuterAliasKind::Type, idx)
        }
    };
    component.outer_aliases.push(OuterAlias {
        kind: alias_kind,
        count,
        index,
        placeholder_index,
    });
}

/// Push a core instance export alias into the appropriate index space
/// on the component.
fn register_core_instance_export(
    component: &mut ParsedComponent,
    instance_index: u32,
    kind: wasmparser::ExternalKind,
    name: String,
) {
    match kind {
        wasmparser::ExternalKind::Func => {
            component.core_funcs.push(CoreFuncDef::AliasInstanceExport {
                instance_index,
                name,
            });
        }
        wasmparser::ExternalKind::Global => {
            component.core_globals.push(CoreAliasDef {
                instance_index,
                name,
            });
        }
        wasmparser::ExternalKind::Memory => {
            component.core_memories.push(CoreAliasDef {
                instance_index,
                name,
            });
        }
        wasmparser::ExternalKind::Table => {
            component.core_tables.push(CoreAliasDef {
                instance_index,
                name,
            });
        }
        wasmparser::ExternalKind::Tag => {
            component.core_tags.push(CoreAliasDef {
                instance_index,
                name,
            });
        }
        // Type aliases are handled separately by wasmparser
        _ => {}
    }
}

/// Push a component instance export alias into the appropriate
/// component-level index space.
///
/// `instance_index` refers to a component instance (not a core instance).
/// The alias creates a new entry in the component-level index space for
/// the given kind.
fn register_component_instance_export(
    component: &mut ParsedComponent,
    instance_index: u32,
    kind: wasmparser::ComponentExternalKind,
    name: String,
) {
    match kind {
        wasmparser::ComponentExternalKind::Func => {
            component
                .component_funcs
                .push(ComponentFuncDef::AliasInstanceExport {
                    instance_index,
                    name,
                });
        }
        wasmparser::ComponentExternalKind::Module => {
            // Core modules aliased from component instance exports.
            // At parse time we insert a placeholder; the actual bytes
            // are resolved at instantiation time.
            let idx = component.core_modules.len() as u32;
            component
                .aliased_core_modules
                .insert(idx, (instance_index, name));
            component.core_modules.push(Vec::new());
        }
        wasmparser::ComponentExternalKind::Instance => {
            component
                .component_instances
                .push(ComponentInstanceDef::AliasInstanceExport {
                    instance_index,
                    name,
                });
        }
        wasmparser::ComponentExternalKind::Type => {
            component.component_types.push(None);
        }
        wasmparser::ComponentExternalKind::Component => {
            // Inner components aliased from component instance exports.
            // At parse time we insert a placeholder; the actual bytes
            // are resolved at instantiation time.
            let idx = component.inner_components.len() as u32;
            component
                .aliased_inner_components
                .insert(idx, (instance_index, name));
            component.inner_components.push(Vec::new());
        }
        _ => {}
    }
}

/// Parse the component-level import section, tracking instance imports.
///
/// Instance imports occupy the first N component instance indices. We count
/// them so that later component instance definitions are indexed correctly.
fn parse_component_import_section(
    component: &mut ParsedComponent,
    reader: wasmparser::ComponentImportSectionReader,
) -> Result<(), String> {
    for import in reader {
        let import = import.map_err(|e| format!("import parse error: {e}"))?;
        let mut required_exports = Vec::new();
        let kind = match import.ty {
            wasmparser::ComponentTypeRef::Instance(type_idx) => {
                component.instance_import_count += 1;
                if let Some(exports) = component.instance_type_exports.get(&type_idx) {
                    required_exports = exports.clone();
                }
                ComponentImportKind::Instance
            }
            wasmparser::ComponentTypeRef::Func(_) => {
                // Func imports occupy a slot in the component func index space.
                component
                    .component_funcs
                    .push(ComponentFuncDef::AliasInstanceExport {
                        instance_index: u32::MAX,
                        name: import.name.0.to_string(),
                    });
                ComponentImportKind::Func
            }
            wasmparser::ComponentTypeRef::Module(_) => {
                // Module imports occupy a slot in the core module index space.
                component.core_modules.push(Vec::new());
                ComponentImportKind::Module
            }
            wasmparser::ComponentTypeRef::Type(bounds) => {
                // Type imports occupy a slot in the component type index space.
                let new_idx = component.component_types.len() as u32;
                component.component_types.push(None);
                // If the type bound is `eq`, propagate the defined type info
                // so that variant case counts flow through type aliases.
                propagate_type_bounds(component, new_idx, bounds);
                ComponentImportKind::Type
            }
            wasmparser::ComponentTypeRef::Component(_) => {
                // Component imports occupy a slot in the inner components
                // index space.
                component.inner_components.push(Vec::new());
                ComponentImportKind::Component
            }
            wasmparser::ComponentTypeRef::Value(_) => ComponentImportKind::Value,
        };
        component.imports.push(ComponentImportDef {
            name: import.name.0.to_string(),
            kind,
            required_exports,
        });
    }
    Ok(())
}

/// Parse the component instance section (component-level instances, not
/// core instances).
fn parse_component_instance_section(
    component: &mut ParsedComponent,
    reader: wasmparser::ComponentInstanceSectionReader,
) -> Result<(), String> {
    for instance in reader {
        let instance = instance.map_err(|e| format!("component instance parse error: {e}"))?;
        match instance {
            wasmparser::ComponentInstance::Instantiate {
                component_index,
                args,
            } => {
                let args = args
                    .iter()
                    .filter_map(|a| {
                        let arg = match a.kind {
                            wasmparser::ComponentExternalKind::Instance => {
                                ComponentInstanceArg::Instance(a.index)
                            }
                            wasmparser::ComponentExternalKind::Module => {
                                ComponentInstanceArg::Module(a.index)
                            }
                            wasmparser::ComponentExternalKind::Component => {
                                ComponentInstanceArg::Component(a.index)
                            }
                            wasmparser::ComponentExternalKind::Func => {
                                ComponentInstanceArg::Func(a.index)
                            }
                            wasmparser::ComponentExternalKind::Type => {
                                ComponentInstanceArg::Type(a.index)
                            }
                            _ => return None,
                        };
                        Some((a.name.to_string(), arg))
                    })
                    .collect();
                component
                    .component_instances
                    .push(ComponentInstanceDef::Instantiate {
                        component_index,
                        args,
                    });
            }
            wasmparser::ComponentInstance::FromExports(exports) => {
                let entries = exports
                    .iter()
                    .map(|e| {
                        let kind = ComponentExternalKind::from(e.kind);
                        ComponentInstanceExport {
                            name: e.name.0.to_string(),
                            kind,
                            index: e.index,
                        }
                    })
                    .collect();
                component
                    .component_instances
                    .push(ComponentInstanceDef::FromExports(entries));
            }
        }
    }
    Ok(())
}

fn parse_canonical_section(
    component: &mut ParsedComponent,
    reader: wasmparser::ComponentCanonicalSectionReader,
) -> Result<(), String> {
    for canonical in reader {
        let canonical = canonical.map_err(|e| format!("canonical parse error: {e}"))?;
        match canonical {
            wasmparser::CanonicalFunction::Lift {
                core_func_index,
                type_index,
                options,
            } => {
                parse_canon_lift(component, core_func_index, type_index, &options);
            }
            wasmparser::CanonicalFunction::Lower {
                func_index,
                options,
            } => {
                let string_encoding = parse_string_encoding(&options);
                let memory_index = options.iter().find_map(|opt| match opt {
                    wasmparser::CanonicalOption::Memory(idx) => Some(*idx),
                    _ => None,
                });
                component.core_funcs.push(CoreFuncDef::Lower {
                    func_index,
                    string_encoding,
                    memory_index,
                });
            }
            wasmparser::CanonicalFunction::ResourceNew { resource } => {
                component
                    .core_funcs
                    .push(CoreFuncDef::ResourceNew { resource });
            }
            wasmparser::CanonicalFunction::ResourceRep { resource } => {
                component
                    .core_funcs
                    .push(CoreFuncDef::ResourceRep { resource });
            }
            wasmparser::CanonicalFunction::ResourceDrop { resource }
            | wasmparser::CanonicalFunction::ResourceDropAsync { resource } => {
                component
                    .core_funcs
                    .push(CoreFuncDef::ResourceDrop { resource });
            }
            // All other canonical builtins (async, threads, etc.) are
            // placeholders — they occupy a core func index slot but we
            // don't implement their semantics yet.
            _ => {
                component.core_funcs.push(CoreFuncDef::AsyncBuiltin);
            }
        }
    }
    Ok(())
}

/// Parse a `canon lift` entry, extracting memory and realloc options.
fn parse_canon_lift(
    component: &mut ParsedComponent,
    core_func_index: u32,
    type_index: u32,
    options: &[wasmparser::CanonicalOption],
) {
    let memory_index = options.iter().find_map(|opt| match opt {
        wasmparser::CanonicalOption::Memory(idx) => Some(*idx),
        _ => None,
    });
    let realloc_func_index = options.iter().find_map(|opt| match opt {
        wasmparser::CanonicalOption::Realloc(idx) => Some(*idx),
        _ => None,
    });
    component.component_funcs.push(ComponentFuncDef::Lift {
        core_func_index,
        type_index,
        memory_index,
        realloc_func_index,
    });
}

/// Extract the string encoding from canonical options.
///
/// Defaults to UTF-8 if no encoding option is specified.
fn parse_string_encoding(options: &[wasmparser::CanonicalOption]) -> StringEncoding {
    for opt in options {
        match opt {
            wasmparser::CanonicalOption::UTF16 => return StringEncoding::Utf16,
            wasmparser::CanonicalOption::CompactUTF16 => return StringEncoding::Latin1Utf16,
            _ => {}
        }
    }
    StringEncoding::Utf8
}

/// Component exports introduce a new item in the corresponding index space.
///
/// For example, `(export "a" (instance 0))` creates a new component instance
/// that aliases instance 0. This mirrors the spec behavior where each export
/// contributes to its kind's index space.
fn register_export_index_space(
    component: &mut ParsedComponent,
    kind: &ComponentExternalKind,
    index: u32,
) {
    match kind {
        ComponentExternalKind::Instance => {
            component
                .component_instances
                .push(ComponentInstanceDef::Reexport {
                    source_index: index,
                });
        }
        ComponentExternalKind::Func => {
            // Func exports reference an existing component func index.
            // No new entry needed — the export def already stores the index.
        }
        ComponentExternalKind::Module => {
            // Module exports introduce a new core module index that is
            // an alias of the existing module at `index`.
            let new_idx = component.core_modules.len() as u32;
            // If the source is itself an alias, propagate the alias info
            if let Some(alias_info) = component.aliased_core_modules.get(&index) {
                component
                    .aliased_core_modules
                    .insert(new_idx, alias_info.clone());
                component.core_modules.push(Vec::new());
            } else if let Some(bytes) = component.core_modules.get(index as usize) {
                component.core_modules.push(bytes.clone());
            } else {
                component.core_modules.push(Vec::new());
            }
        }
        ComponentExternalKind::Type => {
            let new_idx = component.component_types.len() as u32;
            component.component_types.push(None);
            // Propagate defined value type info from the source type.
            if let Some(val_type) = component.defined_val_types.get(&index).copied() {
                component.defined_val_types.insert(new_idx, val_type);
            }
        }
        _ => {}
    }
}

fn parse_export_section(
    component: &mut ParsedComponent,
    reader: wasmparser::ComponentExportSectionReader,
) -> Result<(), String> {
    for export in reader {
        let export = export.map_err(|e| format!("export parse error: {e}"))?;
        let kind = ComponentExternalKind::from(export.kind);

        // Component exports introduce a new item in the corresponding
        // index space. The new item references the original at `export.index`.
        register_export_index_space(component, &kind, export.index);

        component.exports.push(ComponentExportDef {
            name: export.name.0.to_string(),
            kind,
            index: export.index,
        });
    }
    Ok(())
}

fn parse_type_section(
    component: &mut ParsedComponent,
    reader: wasmparser::ComponentTypeSectionReader,
) -> Result<(), String> {
    for ty in reader {
        let ty = ty.map_err(|e| format!("type parse error: {e}"))?;
        let type_index = component.component_types.len() as u32;
        match ty {
            wasmparser::ComponentType::Func(func_ty) => {
                let params: Vec<ComponentResultType> = func_ty
                    .params
                    .iter()
                    .map(|(_name, ty)| convert_val_type(component, ty))
                    .collect();
                let result = match func_ty.result {
                    None => ComponentResultType::Unit,
                    Some(ref ty) => convert_val_type(component, ty),
                };
                component
                    .component_types
                    .push(Some(ComponentFuncTypeDef { params, result }));
            }
            wasmparser::ComponentType::Instance(decls) => {
                let export_names = extract_instance_type_exports(&decls);
                if !export_names.is_empty() {
                    component
                        .instance_type_exports
                        .insert(type_index, export_names.clone());
                }
                component.component_types.push(None);
            }
            wasmparser::ComponentType::Defined(def) => {
                record_defined_type(component, type_index, &def);
                component.component_types.push(None);
            }
            _ => {
                // Non-func types get a placeholder
                component.component_types.push(None);
            }
        }
    }
    Ok(())
}

/// Extract export names from an instance type declaration.
///
/// Scans the declarations for `Export` entries and collects their names.
fn extract_instance_type_exports(decls: &[wasmparser::InstanceTypeDeclaration]) -> Vec<String> {
    decls
        .iter()
        .filter_map(|d| match d {
            wasmparser::InstanceTypeDeclaration::Export { name, .. } => Some(name.0.to_string()),
            _ => None,
        })
        .collect()
}

/// Extract module type constraints from instance type declarations.
///
/// Propagate defined value type info through type bounds.
///
/// When a type import has an `eq` bound (e.g. `(import "a" (type $a (eq $a')))`),
/// the imported type is equivalent to the referenced type. If the referenced
/// type is a variant (or other defined type we track), the import inherits
/// that info so that canonical ABI validation works on the aliased type.
fn propagate_type_bounds(
    component: &mut ParsedComponent,
    new_idx: u32,
    bounds: wasmparser::TypeBounds,
) {
    if let wasmparser::TypeBounds::Eq(src_idx) = bounds {
        if let Some(val_type) = component.defined_val_types.get(&src_idx).copied() {
            component.defined_val_types.insert(new_idx, val_type);
        }
    }
}

/// Record a defined component type for later lookup.
///
/// Currently only records variant types (with their case count) so that
/// the canonical ABI can validate discriminant values at runtime.
fn record_defined_type(
    component: &mut ParsedComponent,
    type_index: u32,
    def: &wasmparser::ComponentDefinedType,
) {
    match def {
        wasmparser::ComponentDefinedType::Variant(cases) => {
            component.defined_val_types.insert(
                type_index,
                ComponentResultType::Variant {
                    case_count: cases.len() as u32,
                },
            );
        }
        wasmparser::ComponentDefinedType::Tuple(fields) => {
            let alignment = compute_tuple_alignment(component, fields);
            component
                .defined_val_types
                .insert(type_index, ComponentResultType::Compound { alignment });
        }
        wasmparser::ComponentDefinedType::Record(fields) => {
            let field_types: Vec<wasmparser::ComponentValType> =
                fields.iter().map(|(_, ty)| *ty).collect();
            let alignment = compute_tuple_alignment(component, &field_types);
            component
                .defined_val_types
                .insert(type_index, ComponentResultType::Compound { alignment });
        }
        wasmparser::ComponentDefinedType::List(_) => {
            component
                .defined_val_types
                .insert(type_index, ComponentResultType::Compound { alignment: 4 });
        }
        _ => {}
    }
}

/// Compute the alignment of a tuple type from its field types.
///
/// The alignment of a tuple is the maximum alignment of any of its fields.
/// Falls back to 4 if any field type is unknown (safe default for i32-based
/// compound types).
fn compute_tuple_alignment(
    component: &ParsedComponent,
    fields: &[wasmparser::ComponentValType],
) -> u32 {
    let mut max_align = 1u32;
    for field in fields {
        let align = match field {
            wasmparser::ComponentValType::Primitive(p) => primitive_alignment(*p),
            wasmparser::ComponentValType::Type(idx) => {
                match component.defined_val_types.get(&(*idx as u32)) {
                    Some(ComponentResultType::Compound { alignment }) => *alignment,
                    _ => 4,
                }
            }
        };
        max_align = max_align.max(align);
    }
    max_align
}

/// Return the byte alignment of a primitive component value type.
fn primitive_alignment(p: wasmparser::PrimitiveValType) -> u32 {
    match p {
        wasmparser::PrimitiveValType::Bool
        | wasmparser::PrimitiveValType::S8
        | wasmparser::PrimitiveValType::U8 => 1,
        wasmparser::PrimitiveValType::S16 | wasmparser::PrimitiveValType::U16 => 2,
        wasmparser::PrimitiveValType::S32
        | wasmparser::PrimitiveValType::U32
        | wasmparser::PrimitiveValType::F32
        | wasmparser::PrimitiveValType::Char => 4,
        wasmparser::PrimitiveValType::S64
        | wasmparser::PrimitiveValType::U64
        | wasmparser::PrimitiveValType::F64 => 8,
        wasmparser::PrimitiveValType::String => 4,
        wasmparser::PrimitiveValType::ErrorContext => 4,
    }
}

/// Convert a `ComponentValType` to a `ComponentResultType`, looking up
/// defined types (like variants) when the type is a reference.
fn convert_val_type(
    component: &ParsedComponent,
    ty: &wasmparser::ComponentValType,
) -> ComponentResultType {
    match ty {
        wasmparser::ComponentValType::Primitive(p) => convert_primitive_type(*p),
        wasmparser::ComponentValType::Type(idx) => component
            .defined_val_types
            .get(&(*idx as u32))
            .copied()
            .unwrap_or(ComponentResultType::Unknown),
    }
}

fn convert_primitive_type(p: wasmparser::PrimitiveValType) -> ComponentResultType {
    match p {
        wasmparser::PrimitiveValType::Bool => ComponentResultType::Bool,
        wasmparser::PrimitiveValType::S8 => ComponentResultType::S8,
        wasmparser::PrimitiveValType::U8 => ComponentResultType::U8,
        wasmparser::PrimitiveValType::S16 => ComponentResultType::S16,
        wasmparser::PrimitiveValType::U16 => ComponentResultType::U16,
        wasmparser::PrimitiveValType::S32 => ComponentResultType::S32,
        wasmparser::PrimitiveValType::U32 => ComponentResultType::U32,
        wasmparser::PrimitiveValType::S64 => ComponentResultType::S64,
        wasmparser::PrimitiveValType::U64 => ComponentResultType::U64,
        wasmparser::PrimitiveValType::F32 => ComponentResultType::F32,
        wasmparser::PrimitiveValType::F64 => ComponentResultType::F64,
        wasmparser::PrimitiveValType::Char => ComponentResultType::Char,
        wasmparser::PrimitiveValType::String => ComponentResultType::String,
        wasmparser::PrimitiveValType::ErrorContext => ComponentResultType::Unknown,
    }
}
