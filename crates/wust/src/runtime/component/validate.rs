//! Wasmparser validation and wasmtime-specific restriction checks.
//!
//! These are pure functions that operate on raw bytes — they don't touch
//! any of our parsed types.

/// Validate a component binary with component model features enabled.
pub(crate) fn validate_component(bytes: &[u8]) -> Result<(), String> {
    let mut features = wasmparser::WasmFeatures::default();
    features.set(wasmparser::WasmFeatures::COMPONENT_MODEL, true);
    features.set(wasmparser::WasmFeatures::CM_ASYNC, true);
    features.set(wasmparser::WasmFeatures::CM_ASYNC_STACKFUL, true);
    features.set(wasmparser::WasmFeatures::CM_ASYNC_BUILTINS, true);
    wasmparser::Validator::new_with_features(features)
        .validate_all(bytes)
        .map_err(|e| format!("component validation error: {e}"))?;
    Ok(())
}

/// Maximum allowed nesting depth for component value types.
const MAX_TYPE_NESTING_DEPTH: u32 = 100;

/// Enforce wasmtime-specific restrictions that wasmparser does not check.
///
/// Currently rejects:
/// - Root-level component imports (importing another component)
/// - Root-level component exports (exporting an inner component)
/// - Reexporting an imported function without an implementation
/// - Type nesting deeper than [`MAX_TYPE_NESTING_DEPTH`]
///
/// Tracks nesting depth via Version/End payloads: root-level sections
/// appear at depth 1.
pub(crate) fn validate_component_restrictions(bytes: &[u8]) -> Result<(), String> {
    let parser = wasmparser::Parser::new(0);
    let mut depth: u32 = 0;
    let mut imported_func_count: u32 = 0;
    let mut type_depths: Vec<u32> = Vec::new();
    for payload in parser.parse_all(bytes) {
        let payload = payload.map_err(|e| format!("parse error: {e}"))?;
        match payload {
            wasmparser::Payload::Version { .. } => depth += 1,
            wasmparser::Payload::End(_) => depth -= 1,
            wasmparser::Payload::ComponentImportSection(reader) if depth == 1 => {
                for import in reader {
                    let import = import.map_err(|e| format!("import parse error: {e}"))?;
                    if matches!(import.ty, wasmparser::ComponentTypeRef::Component(_)) {
                        return Err(
                            "root-level component imports are not supported".to_string()
                        );
                    }
                    if matches!(import.ty, wasmparser::ComponentTypeRef::Func(_)) {
                        imported_func_count += 1;
                    }
                }
            }
            wasmparser::Payload::ComponentExportSection(reader) if depth == 1 => {
                for export in reader {
                    let export = export.map_err(|e| format!("export parse error: {e}"))?;
                    if export.kind == wasmparser::ComponentExternalKind::Component {
                        return Err(
                            "exporting a component from the root component is not supported"
                                .to_string(),
                        );
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
            }
            wasmparser::Payload::ComponentTypeSection(reader) if depth == 1 => {
                for ty in reader {
                    let ty = ty.map_err(|e| format!("type parse error: {e}"))?;
                    let d = compute_type_depth(&ty, &type_depths);
                    if d >= MAX_TYPE_NESTING_DEPTH {
                        return Err("type nesting is too deep".to_string());
                    }
                    type_depths.push(d);
                }
            }
            _ => {}
        }
    }
    Ok(())
}

/// Compute the nesting depth of a component type definition.
///
/// Types are defined in order, so each type can only reference
/// previously-defined types. `prior_depths` holds the depth of
/// every type defined so far.
fn compute_type_depth(
    ty: &wasmparser::ComponentType,
    prior_depths: &[u32],
) -> u32 {
    match ty {
        wasmparser::ComponentType::Defined(def) => compute_defined_type_depth(def, prior_depths),
        wasmparser::ComponentType::Func(_) => 0,
        _ => 0,
    }
}

/// Compute the nesting depth of a component defined type.
fn compute_defined_type_depth(
    def: &wasmparser::ComponentDefinedType,
    prior_depths: &[u32],
) -> u32 {
    match def {
        wasmparser::ComponentDefinedType::Primitive(_) => 0,
        wasmparser::ComponentDefinedType::List(inner)
        | wasmparser::ComponentDefinedType::Option(inner) => {
            val_type_depth(inner, prior_depths) + 1
        }
        wasmparser::ComponentDefinedType::Tuple(fields) => {
            fields.iter().map(|f| val_type_depth(f, prior_depths)).max().unwrap_or(0) + 1
        }
        wasmparser::ComponentDefinedType::Record(fields) => {
            fields
                .iter()
                .map(|f| val_type_depth(&f.1, prior_depths))
                .max()
                .unwrap_or(0)
                + 1
        }
        wasmparser::ComponentDefinedType::Variant(cases) => {
            cases
                .iter()
                .filter_map(|c| c.ty.as_ref())
                .map(|ty| val_type_depth(ty, prior_depths))
                .max()
                .unwrap_or(0)
                + 1
        }
        wasmparser::ComponentDefinedType::Result { ok, err } => {
            let ok_depth = ok.as_ref().map(|t| val_type_depth(t, prior_depths)).unwrap_or(0);
            let err_depth = err.as_ref().map(|t| val_type_depth(t, prior_depths)).unwrap_or(0);
            ok_depth.max(err_depth) + 1
        }
        _ => 0,
    }
}

/// Compute the depth contribution of a `ComponentValType`.
fn val_type_depth(ty: &wasmparser::ComponentValType, prior_depths: &[u32]) -> u32 {
    match ty {
        wasmparser::ComponentValType::Primitive(_) => 0,
        wasmparser::ComponentValType::Type(idx) => {
            prior_depths.get(*idx as usize).copied().unwrap_or(0)
        }
    }
}
