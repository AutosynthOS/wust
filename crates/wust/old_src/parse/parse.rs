//! Component binary section parsing.
//!
//! Extracts component sections from raw bytes into our parsed types.

use super::types::*;

// ---------------------------------------------------------------------------
// Section parsing
// ---------------------------------------------------------------------------

/// Validate and parse a component binary.
///
/// Validates the binary with the provided validator (which returns the
/// `Types` object), then extracts structural information into a
/// `ParsedComponent`.
pub(crate) fn parse_and_validate(
    bytes: &[u8],
    validator: &mut wasmparser::Validator,
) -> Result<(ParsedComponent, wasmparser::types::Types), anyhow::Error> {
    let types = validator.validate_all(bytes)?;
    check_type_nesting_depth(&types)?;
    let component = parse_component_sections(bytes)
        .map_err(|e| anyhow::anyhow!(e))?;
    Ok((component, types))
}

const MAX_TYPE_NESTING_DEPTH: u32 = 100;

/// Reject components with type nesting deeper than [`MAX_TYPE_NESTING_DEPTH`].
///
/// wasmparser doesn't enforce a nesting limit, but wasmtime does (to bound
/// recursive canonical ABI operations). We match that limit here.
fn check_type_nesting_depth(types: &wasmparser::types::Types) -> Result<(), anyhow::Error> {
    use wasmparser::component_types::*;

    fn val_type_depth(types: &wasmparser::types::Types, ty: &ComponentValType) -> u32 {
        match ty {
            ComponentValType::Primitive(_) => 0,
            ComponentValType::Type(id) => defined_type_depth(types, *id),
        }
    }

    fn defined_type_depth(
        types: &wasmparser::types::Types,
        id: ComponentDefinedTypeId,
    ) -> u32 {
        let Some(defined) = types.as_ref().get(id) else {
            return 0;
        };
        let inner = match defined {
            ComponentDefinedType::Primitive(_) => 0,
            ComponentDefinedType::List(inner) => val_type_depth(types, inner),
            ComponentDefinedType::Option(inner) => val_type_depth(types, inner),
            ComponentDefinedType::Tuple(t) => t
                .types
                .iter()
                .map(|f| val_type_depth(types, f))
                .max()
                .unwrap_or(0),
            ComponentDefinedType::Record(r) => r
                .fields
                .iter()
                .map(|(_, f)| val_type_depth(types, f))
                .max()
                .unwrap_or(0),
            ComponentDefinedType::Variant(v) => v
                .cases
                .iter()
                .filter_map(|(_, c)| c.ty.as_ref())
                .map(|f| val_type_depth(types, f))
                .max()
                .unwrap_or(0),
            ComponentDefinedType::Result { ok, err } => {
                let ok_d = ok.as_ref().map(|t| val_type_depth(types, t)).unwrap_or(0);
                let err_d = err.as_ref().map(|t| val_type_depth(types, t)).unwrap_or(0);
                ok_d.max(err_d)
            }
            ComponentDefinedType::Map(k, v) => {
                val_type_depth(types, k).max(val_type_depth(types, v))
            }
            ComponentDefinedType::FixedLengthList(inner, _) => val_type_depth(types, inner),
            ComponentDefinedType::Future(inner) | ComponentDefinedType::Stream(inner) => {
                inner.as_ref().map(|t| val_type_depth(types, t)).unwrap_or(0)
            }
            ComponentDefinedType::Flags(_)
            | ComponentDefinedType::Enum(_)
            | ComponentDefinedType::Own(_)
            | ComponentDefinedType::Borrow(_) => 0,
        };
        1 + inner
    }

    let type_count = types.as_ref().component_type_count();
    for i in 0..type_count {
        let any_id = types.as_ref().component_any_type_at(i);
        if let ComponentAnyTypeId::Defined(id) = any_id {
            let depth = defined_type_depth(types, id);
            if depth > MAX_TYPE_NESTING_DEPTH {
                return Err(anyhow::anyhow!("type nesting is too deep"));
            }
        }
    }
    Ok(())
}

/// Parse a component binary into structural information.
///
/// Walks root-level sections and populates a `ParsedComponent` with
/// core modules, instances, funcs, exports, imports, etc.
fn parse_component_sections(bytes: &[u8]) -> Result<ParsedComponent, String> {
    let mut component = ParsedComponent::empty();
    let parser = wasmparser::Parser::new(0);
    let mut depth: u32 = 0;
    let mut imported_func_count: u32 = 0;

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
        dispatch_section(&mut component, payload, bytes, &mut imported_func_count)?;
    }
    Ok(component)
}

/// Dispatch a single root-level payload to the appropriate section parser.
fn dispatch_section(
    component: &mut ParsedComponent,
    payload: wasmparser::Payload,
    bytes: &[u8],
    imported_func_count: &mut u32,
) -> Result<(), String> {
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
            check_export_restrictions(reader.clone(), *imported_func_count)?;
            parse_export_section(component, reader)?;
        }
        wasmparser::Payload::ComponentTypeSection(reader) => {
            count_types(component, reader)?;
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
            check_import_restrictions(reader.clone(), imported_func_count)?;
            parse_component_import_section(component, reader)?;
        }
        _ => {}
    }
    Ok(())
}

/// Reject unsupported root-level component imports and count func imports.
fn check_import_restrictions(
    reader: wasmparser::ComponentImportSectionReader,
    imported_func_count: &mut u32,
) -> Result<(), String> {
    for import in reader {
        let import = import.map_err(|e| format!("import parse error: {e}"))?;
        if matches!(import.ty, wasmparser::ComponentTypeRef::Component(_)) {
            return Err("root-level component imports are not supported".into());
        }
        if matches!(import.ty, wasmparser::ComponentTypeRef::Func(_)) {
            *imported_func_count += 1;
        }
    }
    Ok(())
}

/// Reject unsupported root-level component exports and func reexports.
fn check_export_restrictions(
    reader: wasmparser::ComponentExportSectionReader,
    imported_func_count: u32,
) -> Result<(), String> {
    for export in reader {
        let export = export.map_err(|e| format!("export parse error: {e}"))?;
        if export.kind == wasmparser::ComponentExternalKind::Component {
            return Err("exporting a component from the root component is not supported".into());
        }
        if export.kind == wasmparser::ComponentExternalKind::Func
            && export.index < imported_func_count
        {
            return Err(format!(
                "component export `{}` is a reexport of an imported \
                 function which is not implemented",
                export.name.0
            ));
        }
    }
    Ok(())
}

/// Count type entries to maintain the type index space.
///
/// We don't store type definitions — the validator's `Types` object
/// provides all type information at runtime. We just need to track
/// instance type exports for import validation.
fn count_types(
    component: &mut ParsedComponent,
    reader: wasmparser::ComponentTypeSectionReader,
) -> Result<(), String> {
    for ty in reader {
        let ty = ty.map_err(|e| format!("type parse error: {e}"))?;
        let type_index = component.component_type_count;
        component.component_type_count += 1;

        // Extract instance type export names for import validation.
        if let wasmparser::ComponentType::Instance(decls) = ty {
            let export_names: Vec<String> = decls
                .iter()
                .filter_map(|d| match d {
                    wasmparser::InstanceTypeDeclaration::Export { name, .. } => {
                        Some(name.0.to_string())
                    }
                    _ => None,
                })
                .collect();
            if !export_names.is_empty() {
                component
                    .instance_type_exports
                    .insert(type_index, export_names);
            }
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
            wasmparser::ComponentAlias::Outer { kind, .. } => {
                register_outer_alias(component, kind);
            }
        }
    }
    Ok(())
}

/// Insert a placeholder in the appropriate index space for an outer alias.
fn register_outer_alias(
    component: &mut ParsedComponent,
    kind: wasmparser::ComponentOuterAliasKind,
) {
    match kind {
        wasmparser::ComponentOuterAliasKind::CoreModule => {
            component.core_modules.push(Vec::new());
        }
        wasmparser::ComponentOuterAliasKind::Component => {
            component.inner_components.push(Vec::new());
        }
        wasmparser::ComponentOuterAliasKind::CoreType => {}
        wasmparser::ComponentOuterAliasKind::Type => {
            component.component_type_count += 1;
        }
    }
}

/// Push a core instance export alias into the appropriate index space.
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
        _ => {}
    }
}

/// Push a component instance export alias into the appropriate index space.
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
            component.core_modules.push(Vec::new());
        }
        wasmparser::ComponentExternalKind::Instance => {
            component
                .component_instances
                .push(ComponentInstanceDef::AliasInstanceExport);
        }
        wasmparser::ComponentExternalKind::Type => {
            component.component_type_count += 1;
        }
        wasmparser::ComponentExternalKind::Component => {
            component.inner_components.push(Vec::new());
        }
        _ => {}
    }
}

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
                component
                    .component_funcs
                    .push(ComponentFuncDef::AliasInstanceExport {
                        instance_index: u32::MAX,
                        name: import.name.0.to_string(),
                    });
                ComponentImportKind::Func
            }
            wasmparser::ComponentTypeRef::Module(_) => {
                component.core_modules.push(Vec::new());
                ComponentImportKind::Module
            }
            wasmparser::ComponentTypeRef::Type(_) => {
                component.component_type_count += 1;
                ComponentImportKind::Type
            }
            wasmparser::ComponentTypeRef::Component(_) => {
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
                                ComponentInstanceArg::Type(())
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

/// Register export in the appropriate index space.
fn register_export_index_space(
    component: &mut ParsedComponent,
    kind: &ComponentExternalKind,
    index: u32,
) {
    match kind {
        ComponentExternalKind::Instance => {
            component
                .component_instances
                .push(ComponentInstanceDef::Reexport);
        }
        ComponentExternalKind::Module => {
            if let Some(bytes) = component.core_modules.get(index as usize) {
                component.core_modules.push(bytes.clone());
            } else {
                component.core_modules.push(Vec::new());
            }
        }
        ComponentExternalKind::Type => {
            component.component_type_count += 1;
        }
        ComponentExternalKind::Func => {
            // Exporting a func creates a new entry in the component func
            // index space that aliases the original func.
            if let Some(original) = component.component_funcs.get(index as usize) {
                let cloned = original.clone();
                component.component_funcs.push(cloned);
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
        register_export_index_space(component, &kind, export.index);
        component.exports.push(ComponentExportDef {
            name: export.name.0.to_string(),
            kind,
            index: export.index,
        });
    }
    Ok(())
}
