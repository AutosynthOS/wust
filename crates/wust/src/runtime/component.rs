use std::collections::HashMap;

use crate::runtime::exec;
use crate::runtime::module::{ExportKind, ImportKind, Module};
use crate::runtime::store::{HostFunc, Store};
use crate::runtime::value::Value;

// ---------------------------------------------------------------------------
// Parsed component definitions (immutable "code" side)
// ---------------------------------------------------------------------------

/// How a core instance is created within a component.
enum CoreInstanceDef {
    /// Instantiate a core module, optionally with import args.
    Instantiate {
        module_index: u32,
        /// Each arg maps a module import namespace to a core instance index.
        args: Vec<(String, CoreInstanceArg)>,
    },
    /// Build a synthetic instance from explicit exports.
    FromExports(Vec<CoreInstanceExportDef>),
}

/// An arg to a core module instantiation — currently always an instance.
#[derive(Clone)]
enum CoreInstanceArg {
    Instance(u32),
}

/// An export in a `FromExports` instance definition.
///
/// Each entry says "export `name` as the core item of `kind` at `index`
/// in the component's core index space for that kind."
#[allow(dead_code)]
struct CoreInstanceExportDef {
    name: String,
    kind: wasmparser::ExternalKind,
    index: u32,
}

/// Trait for alias definitions that reference a core instance export.
///
/// All four core alias types (func, global, memory, table) share the same
/// shape: an instance index and an export name. This trait provides uniform
/// access to those coordinates.
trait AliasInstanceExportDef {
    fn instance_index(&self) -> u32;
    fn name(&self) -> &str;
}

/// How a core func is resolved — via an alias from a core instance export.
enum CoreFuncDef {
    AliasInstanceExport { instance_index: u32, name: String },
}

/// How a core global is resolved — via an alias from a core instance export.
enum CoreGlobalDef {
    AliasInstanceExport { instance_index: u32, name: String },
}

/// How a core memory is resolved — via an alias from a core instance export.
enum CoreMemoryDef {
    AliasInstanceExport { instance_index: u32, name: String },
}

/// How a core table is resolved — via an alias from a core instance export.
enum CoreTableDef {
    AliasInstanceExport { instance_index: u32, name: String },
}

/// Implement `AliasInstanceExportDef` for each core alias type via a macro,
/// since they all have an identical single-variant structure.
macro_rules! impl_alias_export {
    ($ty:ident) => {
        impl AliasInstanceExportDef for $ty {
            fn instance_index(&self) -> u32 {
                let Self::AliasInstanceExport { instance_index, .. } = self;
                *instance_index
            }
            fn name(&self) -> &str {
                let Self::AliasInstanceExport { name, .. } = self;
                name
            }
        }
    };
}

impl_alias_export!(CoreFuncDef);
impl_alias_export!(CoreGlobalDef);
impl_alias_export!(CoreMemoryDef);
impl_alias_export!(CoreTableDef);

/// Simplified component value type for canonical ABI lifting.
#[derive(Debug, Clone, Copy)]
pub enum ComponentResultType {
    Bool,
    S8,
    U8,
    S16,
    U16,
    S32,
    U32,
    S64,
    U64,
    F32,
    F64,
    Char,
    String,
    /// No result (unit function).
    Unit,
    /// A type we don't yet handle — pass through raw.
    Unknown,
}

/// A lifted component function backed by a core function.
struct ComponentFuncDef {
    core_func_index: u32,
    type_index: u32,
}

/// A component-level export.
struct ComponentExportDef {
    name: String,
    kind: ComponentExternalKind,
    index: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ComponentExternalKind {
    Func,
    Module,
    Component,
    Instance,
    Value,
    Type,
}

/// A parsed component — immutable "code" side, analogous to `Module`.
pub struct Component {
    core_modules: Vec<Vec<u8>>,
    core_instances: Vec<CoreInstanceDef>,
    core_funcs: Vec<CoreFuncDef>,
    core_globals: Vec<CoreGlobalDef>,
    core_memories: Vec<CoreMemoryDef>,
    core_tables: Vec<CoreTableDef>,
    component_funcs: Vec<ComponentFuncDef>,
    exports: Vec<ComponentExportDef>,
    /// Component-level types. Only func types are stored; other type
    /// indices map to `None`.
    component_types: Vec<Option<ComponentFuncTypeDef>>,
}

/// A parsed component function type (params + result).
struct ComponentFuncTypeDef {
    result: ComponentResultType,
}

impl Component {
    /// Parse a component binary into a `Component`.
    ///
    /// Validates the binary with component features enabled, then extracts
    /// the sections needed for instantiation and invocation.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        validate_component(bytes)?;
        validate_component_restrictions(bytes)?;

        let mut component = Component {
            core_modules: Vec::new(),
            core_instances: Vec::new(),
            core_funcs: Vec::new(),
            core_globals: Vec::new(),
            core_memories: Vec::new(),
            core_tables: Vec::new(),
            component_funcs: Vec::new(),
            exports: Vec::new(),
            component_types: Vec::new(),
        };

        parse_component_sections(&mut component, bytes)?;
        Ok(component)
    }
}

// ---------------------------------------------------------------------------
// Validation and top-level parsing
// ---------------------------------------------------------------------------

/// Validate a component binary with component model features enabled.
fn validate_component(bytes: &[u8]) -> Result<(), String> {
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
fn validate_component_restrictions(bytes: &[u8]) -> Result<(), String> {
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

/// Walk all payloads in a component binary and dispatch each recognized
/// section to the appropriate parser.
fn parse_component_sections(component: &mut Component, bytes: &[u8]) -> Result<(), String> {
    let parser = wasmparser::Parser::new(0);
    for payload in parser.parse_all(bytes) {
        let payload = payload.map_err(|e| format!("parse error: {e}"))?;
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
            _ => {}
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Section parsers
// ---------------------------------------------------------------------------

fn parse_instance_section(
    component: &mut Component,
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
    component: &mut Component,
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
            // Component-level aliases (outer, etc.) — not yet supported
            _ => {}
        }
    }
    Ok(())
}

/// Push a core instance export alias into the appropriate index space
/// on the component.
fn register_core_instance_export(
    component: &mut Component,
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
            component
                .core_globals
                .push(CoreGlobalDef::AliasInstanceExport {
                    instance_index,
                    name,
                });
        }
        wasmparser::ExternalKind::Memory => {
            component
                .core_memories
                .push(CoreMemoryDef::AliasInstanceExport {
                    instance_index,
                    name,
                });
        }
        wasmparser::ExternalKind::Table => {
            component
                .core_tables
                .push(CoreTableDef::AliasInstanceExport {
                    instance_index,
                    name,
                });
        }
        // Type aliases are handled separately by wasmparser
        _ => {}
    }
}

fn parse_canonical_section(
    component: &mut Component,
    reader: wasmparser::ComponentCanonicalSectionReader,
) -> Result<(), String> {
    for canonical in reader {
        let canonical = canonical.map_err(|e| format!("canonical parse error: {e}"))?;
        match canonical {
            wasmparser::CanonicalFunction::Lift {
                core_func_index,
                type_index,
                ..
            } => {
                component.component_funcs.push(ComponentFuncDef {
                    core_func_index,
                    type_index,
                });
            }
            _ => {}
        }
    }
    Ok(())
}

fn parse_export_section(
    component: &mut Component,
    reader: wasmparser::ComponentExportSectionReader,
) -> Result<(), String> {
    for export in reader {
        let export = export.map_err(|e| format!("export parse error: {e}"))?;
        let kind = match export.kind {
            wasmparser::ComponentExternalKind::Func => ComponentExternalKind::Func,
            wasmparser::ComponentExternalKind::Module => ComponentExternalKind::Module,
            wasmparser::ComponentExternalKind::Component => ComponentExternalKind::Component,
            wasmparser::ComponentExternalKind::Instance => ComponentExternalKind::Instance,
            wasmparser::ComponentExternalKind::Value => ComponentExternalKind::Value,
            wasmparser::ComponentExternalKind::Type => ComponentExternalKind::Type,
        };
        component.exports.push(ComponentExportDef {
            name: export.name.0.to_string(),
            kind,
            index: export.index,
        });
    }
    Ok(())
}

fn parse_type_section(
    component: &mut Component,
    reader: wasmparser::ComponentTypeSectionReader,
) -> Result<(), String> {
    for ty in reader {
        let ty = ty.map_err(|e| format!("type parse error: {e}"))?;
        match ty {
            wasmparser::ComponentType::Func(func_ty) => {
                let result = match func_ty.result {
                    None => ComponentResultType::Unit,
                    Some(wasmparser::ComponentValType::Primitive(p)) => convert_primitive_type(p),
                    Some(wasmparser::ComponentValType::Type(_)) => ComponentResultType::Unknown,
                };
                component
                    .component_types
                    .push(Some(ComponentFuncTypeDef { result }));
            }
            _ => {
                // Non-func types get a placeholder
                component.component_types.push(None);
            }
        }
    }
    Ok(())
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

// ---------------------------------------------------------------------------
// Live instance state
// ---------------------------------------------------------------------------

/// A resolved export from a core instance.
#[derive(Clone)]
#[allow(dead_code)]
enum CoreExport {
    Func { instance: usize, index: u32 },
    Global { instance: usize, index: u32 },
    Memory { instance: usize, index: u32 },
    Table { instance: usize, index: u32 },
}

/// Convert an `ExportKind` into a `CoreExport` tagged with the source
/// instance index and export index.
fn make_core_export(kind: &ExportKind, instance: usize, index: u32) -> CoreExport {
    match kind {
        ExportKind::Func => CoreExport::Func { instance, index },
        ExportKind::Global => CoreExport::Global { instance, index },
        ExportKind::Memory => CoreExport::Memory { instance, index },
        ExportKind::Table => CoreExport::Table { instance, index },
    }
}

/// A live core instance — either a real instantiated module or a synthetic
/// bag of exports.
enum CoreInstance {
    Instantiated {
        module: Module,
        store: Store,
    },
    Synthetic {
        exports: HashMap<String, CoreExport>,
    },
}

impl CoreInstance {
    /// Look up an export by name, returning its kind and index.
    ///
    /// For `Instantiated` instances, the index is the export's position
    /// in the module's index space. For `Synthetic` instances, the caller
    /// should use `ComponentInstance::resolve_core_export` instead to get
    /// the full `CoreExport` with the real instance index.
    fn resolve_export(&self, name: &str) -> Option<(ExportKind, u32)> {
        match self {
            CoreInstance::Instantiated { module, .. } => module
                .exports
                .iter()
                .find(|e| e.name == name)
                .map(|e| (e.kind.clone(), e.index)),
            CoreInstance::Synthetic { exports } => exports.get(name).map(|ce| match ce {
                CoreExport::Func { index, .. } => (ExportKind::Func, *index),
                CoreExport::Global { index, .. } => (ExportKind::Global, *index),
                CoreExport::Memory { index, .. } => (ExportKind::Memory, *index),
                CoreExport::Table { index, .. } => (ExportKind::Table, *index),
            }),
        }
    }
}

/// A resolved component function — points to a specific core instance and func.
struct ResolvedFunc {
    core_instance_index: usize,
    core_func_index: u32,
    result_type: ComponentResultType,
}

/// A live component instance — analogous to `Store` for core modules.
pub struct ComponentInstance {
    core_instances: Vec<CoreInstance>,
    exports: HashMap<String, ResolvedFunc>,
}

impl ComponentInstance {
    /// Instantiate a parsed component, creating all core instances and
    /// resolving exports.
    ///
    /// # Algorithm
    ///
    /// 1. For each `CoreInstanceDef`:
    ///    - `Instantiate`: parse the core module, collect imports from
    ///      the arg instances, create a `Store` with those imports, run
    ///      the start function if present.
    ///    - `FromExports`: build a synthetic instance that maps export
    ///      names to exports from other core instances.
    /// 2. Resolve component-level exports by following the chain:
    ///    component export → component func (canon lift) → core func
    ///    (alias) → core instance export → actual func index.
    pub fn instantiate(component: &Component) -> Result<Self, String> {
        let mut inst = ComponentInstance {
            core_instances: Vec::new(),
            exports: HashMap::new(),
        };

        for def in &component.core_instances {
            match def {
                CoreInstanceDef::Instantiate { module_index, args } => {
                    instantiate_core_module(&mut inst, component, *module_index, args)?;
                }
                CoreInstanceDef::FromExports(export_defs) => {
                    build_synthetic_instance(&mut inst, component, export_defs)?;
                }
            }
        }

        resolve_component_exports(&mut inst, component)?;
        Ok(inst)
    }

    /// Invoke a named component function, returning core values and
    /// the canonical result type for lifting.
    pub fn invoke(
        &mut self,
        name: &str,
        args: &[Value],
    ) -> Result<(Vec<Value>, ComponentResultType), String> {
        let resolved = self
            .exports
            .get(name)
            .ok_or_else(|| format!("export '{}' not found", name))?;
        let idx = resolved.core_instance_index;
        let func_idx = resolved.core_func_index;
        let result_type = resolved.result_type;
        let instance = self
            .core_instances
            .get_mut(idx)
            .ok_or_else(|| format!("core instance {} out of bounds", idx))?;
        match instance {
            CoreInstance::Instantiated { module, store } => {
                let values =
                    exec::call(module, store, func_idx, args).map_err(|e| format!("trap: {e}"))?;
                Ok((values, result_type))
            }
            CoreInstance::Synthetic { .. } => {
                Err("cannot invoke function on synthetic instance".into())
            }
        }
    }

    /// Resolve a named export from a core instance to a full `CoreExport`.
    ///
    /// For `Instantiated` instances, wraps the (kind, index) with the given
    /// instance index. For `Synthetic` instances, returns the stored
    /// `CoreExport` directly — it already carries the real instance index.
    fn resolve_core_export(&self, instance_idx: usize, name: &str) -> Option<CoreExport> {
        match self.core_instances.get(instance_idx)? {
            CoreInstance::Instantiated { module, .. } => module
                .exports
                .iter()
                .find(|e| e.name == name)
                .map(|e| make_core_export(&e.kind, instance_idx, e.index)),
            CoreInstance::Synthetic { exports } => exports.get(name).cloned(),
        }
    }
}

// ---------------------------------------------------------------------------
// Instantiation helpers
// ---------------------------------------------------------------------------

/// Instantiate a core module, wiring up imports from the arg instances.
///
/// For each import the module declares, we look up the matching arg
/// instance and find the corresponding export. Func imports become
/// host function trampolines that call back into the source instance.
/// Global imports are copied by value. Memory and table imports are
/// not yet supported (they require shared state).
fn instantiate_core_module(
    inst: &mut ComponentInstance,
    component: &Component,
    module_index: u32,
    args: &[(String, CoreInstanceArg)],
) -> Result<(), String> {
    let module_bytes = component
        .core_modules
        .get(module_index as usize)
        .ok_or_else(|| format!("module index {} out of bounds", module_index))?;
    let module = Module::from_bytes(module_bytes)?;

    let (host_funcs, imported_globals) = resolve_imports(&module, args, inst)?;
    let mut store = Store::new_with_imports(&module, host_funcs, imported_globals)?;

    if let Some(start_idx) = module.start {
        exec::call(&module, &mut store, start_idx, &[])
            .map_err(|e| format!("start function trap: {e}"))?;
    }

    inst.core_instances
        .push(CoreInstance::Instantiated { module, store });
    Ok(())
}

/// Resolve a module's imports against the provided arg instances.
///
/// Returns (host_funcs, imported_globals) suitable for `Store::new_with_imports`.
fn resolve_imports(
    module: &Module,
    args: &[(String, CoreInstanceArg)],
    inst: &ComponentInstance,
) -> Result<(Vec<HostFunc>, Vec<Value>), String> {
    let mut host_funcs: Vec<HostFunc> = Vec::new();
    let mut imported_globals: Vec<Value> = Vec::new();

    for import in &module.imports {
        resolve_single_import(import, args, inst, &mut host_funcs, &mut imported_globals)?;
    }

    Ok((host_funcs, imported_globals))
}

/// Resolve one module import against the arg instances, appending to the
/// appropriate output vector.
///
/// If no arg matches the import's namespace, a default value is provided
/// (no-op trampoline for funcs, zero for globals). Otherwise, the export
/// is looked up in the source instance and wired in.
fn resolve_single_import(
    import: &crate::runtime::module::Import,
    args: &[(String, CoreInstanceArg)],
    inst: &ComponentInstance,
    host_funcs: &mut Vec<HostFunc>,
    imported_globals: &mut Vec<Value>,
) -> Result<(), String> {
    let arg_instance_idx = find_arg_instance(args, &import.module);

    let Some(arg_idx) = arg_instance_idx else {
        provide_default_import(import, host_funcs, imported_globals);
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
            host_funcs.push(make_trampoline(arg_idx, export_index));
        }
        (ImportKind::Global { .. }, ExportKind::Global) => {
            let val = get_global_value(inst, arg_idx, export_index)?;
            imported_globals.push(val);
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

/// Provide default values for an import that has no matching arg instance.
fn provide_default_import(
    import: &crate::runtime::module::Import,
    host_funcs: &mut Vec<HostFunc>,
    imported_globals: &mut Vec<Value>,
) {
    match &import.kind {
        ImportKind::Func(_) => {
            host_funcs.push(Box::new(|_args, _mem| Vec::new()));
        }
        ImportKind::Global { .. } => {
            imported_globals.push(Value::I32(0));
        }
        _ => {}
    }
}

/// Create a host function trampoline that, when called, invokes a function
/// in another core instance.
///
/// Since we can't hold a mutable reference to the source instance during
/// execution (the caller's instance is also borrowed), we defer the actual
/// call. The trampoline captures the source coordinates and the call is
/// dispatched via the component instance's shared state.
///
/// For now, we return a no-op trampoline that returns empty results.
/// Full cross-instance calls require refactoring Store to use interior
/// mutability. This is sufficient for modules whose imported functions
/// are never actually called (e.g., the start function only calls its
/// own functions or checks globals).
fn make_trampoline(_src_inst: usize, _src_func: u32) -> HostFunc {
    // TODO: implement real cross-instance function calls
    Box::new(|_args, _mem| Vec::new())
}

/// Read a global value from a core instance.
fn get_global_value(
    inst: &ComponentInstance,
    instance_idx: usize,
    global_idx: u32,
) -> Result<Value, String> {
    match inst.core_instances.get(instance_idx) {
        Some(CoreInstance::Instantiated { store, .. }) => store
            .globals
            .get(global_idx as usize)
            .copied()
            .ok_or_else(|| format!("global {} out of bounds", global_idx)),
        Some(CoreInstance::Synthetic { .. }) => {
            Err("cannot read global from synthetic instance".into())
        }
        None => Err(format!("instance {} out of bounds", instance_idx)),
    }
}

/// Build a synthetic core instance from explicit exports.
///
/// Each `CoreInstanceExportDef` references an item in the component's core
/// index space (funcs, globals, memories, tables). We look up the alias
/// definition to find which instance and export name it came from, then
/// resolve that against the live instances to produce a `CoreExport`.
fn build_synthetic_instance(
    inst: &mut ComponentInstance,
    component: &Component,
    export_defs: &[CoreInstanceExportDef],
) -> Result<(), String> {
    let mut exports = HashMap::new();

    for def in export_defs {
        let core_export = resolve_alias_to_core_export(inst, component, def.kind, def.index)?;
        exports.insert(def.name.clone(), core_export);
    }

    inst.core_instances
        .push(CoreInstance::Synthetic { exports });
    Ok(())
}

/// Look up an alias def by index in a slice, returning its coordinates.
///
/// Returns `(instance_index, name)` or a descriptive error if the index is
/// out of bounds.
fn get_alias_coords<'a, T: AliasInstanceExportDef>(
    aliases: &'a [T],
    index: u32,
    label: &str,
) -> Result<(u32, &'a str), String> {
    let alias = aliases
        .get(index as usize)
        .ok_or_else(|| format!("core {} alias index {} out of bounds", label, index))?;
    Ok((alias.instance_index(), alias.name()))
}

/// Resolve an alias reference (kind + index in the component's core index
/// space) to a live `CoreExport`.
fn resolve_alias_to_core_export(
    inst: &ComponentInstance,
    component: &Component,
    kind: wasmparser::ExternalKind,
    index: u32,
) -> Result<CoreExport, String> {
    let (instance_index, name) = match kind {
        wasmparser::ExternalKind::Func => get_alias_coords(&component.core_funcs, index, "func")?,
        wasmparser::ExternalKind::Global => {
            get_alias_coords(&component.core_globals, index, "global")?
        }
        wasmparser::ExternalKind::Memory => {
            get_alias_coords(&component.core_memories, index, "memory")?
        }
        wasmparser::ExternalKind::Table => {
            get_alias_coords(&component.core_tables, index, "table")?
        }
        _ => return Err("unsupported export kind in synthetic instance".to_string()),
    };
    resolve_aliased_export(inst, instance_index, name, kind)
}

/// Look up a core export by instance index and name, returning a
/// descriptive error on failure.
fn resolve_aliased_export(
    inst: &ComponentInstance,
    instance_index: u32,
    name: &str,
    kind: wasmparser::ExternalKind,
) -> Result<CoreExport, String> {
    let label = match kind {
        wasmparser::ExternalKind::Func => "func",
        wasmparser::ExternalKind::Global => "global",
        wasmparser::ExternalKind::Memory => "memory",
        wasmparser::ExternalKind::Table => "table",
        _ => "unknown",
    };
    inst.resolve_core_export(instance_index as usize, name)
        .ok_or_else(|| {
            format!(
                "{} export '{}' not found in instance {}",
                label, name, instance_index
            )
        })
}

/// Resolve component-level exports by following the chain:
/// component export → component func → core func alias → core instance export.
fn resolve_component_exports(
    inst: &mut ComponentInstance,
    component: &Component,
) -> Result<(), String> {
    for export_def in &component.exports {
        if export_def.kind != ComponentExternalKind::Func {
            continue;
        }
        resolve_single_export(inst, component, export_def)?;
    }
    Ok(())
}

/// Resolve one component-level func export into the instance's export map.
///
/// Follows the chain: component func (canon lift) → core func alias →
/// core instance export, then inserts the resolved func.
fn resolve_single_export(
    inst: &mut ComponentInstance,
    component: &Component,
    export_def: &ComponentExportDef,
) -> Result<(), String> {
    let comp_func = component
        .component_funcs
        .get(export_def.index as usize)
        .ok_or_else(|| format!("component func index {} out of bounds", export_def.index))?;

    let core_func = component
        .core_funcs
        .get(comp_func.core_func_index as usize)
        .ok_or_else(|| {
            format!(
                "core func index {} out of bounds",
                comp_func.core_func_index
            )
        })?;

    let result_type = lookup_result_type(component, comp_func.type_index);
    let resolved = resolve_core_func_export(inst, core_func, result_type)?;
    inst.exports.insert(export_def.name.clone(), resolved);
    Ok(())
}

/// Follow a core func alias to its live instance, returning a `ResolvedFunc`.
fn resolve_core_func_export(
    inst: &ComponentInstance,
    core_func: &CoreFuncDef,
    result_type: ComponentResultType,
) -> Result<ResolvedFunc, String> {
    let instance_index = core_func.instance_index();
    let name = core_func.name();
    match inst.resolve_core_export(instance_index as usize, name) {
        Some(CoreExport::Func {
            instance: real_inst,
            index: func_idx,
        }) => Ok(ResolvedFunc {
            core_instance_index: real_inst,
            core_func_index: func_idx,
            result_type,
        }),
        _ => Err(format!("core export '{}' not found or not a func", name)),
    }
}

/// Look up the result type from a component func type index.
fn lookup_result_type(component: &Component, type_index: u32) -> ComponentResultType {
    component
        .component_types
        .get(type_index as usize)
        .and_then(|t| t.as_ref())
        .map(|t| t.result)
        .unwrap_or(ComponentResultType::Unknown)
}
