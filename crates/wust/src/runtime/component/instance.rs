//! Live component instance state and instantiation logic.
//!
//! Contains `ComponentInstance` (analogous to `Store` for core modules)
//! and the core types for representing live core instances, resolved
//! exports, and resource handles.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::rc::Rc;

use crate::runtime::canonical_abi;
use crate::runtime::exec;
use crate::runtime::module::{ExportKind, Module};
use crate::runtime::store::SharedStore;
use crate::runtime::value::Value;

use super::imports;
use crate::parse::types::*;

// ---------------------------------------------------------------------------
// Live core instance state
// ---------------------------------------------------------------------------

/// A resolved export from a core instance.
#[derive(Clone, Debug)]
#[allow(dead_code)]
pub(crate) enum CoreExport {
    Func {
        instance: usize,
        index: u32,
    },
    Global {
        instance: usize,
        index: u32,
    },
    Memory {
        instance: usize,
        index: u32,
    },
    Table {
        instance: usize,
        index: u32,
    },
    Tag {
        instance: usize,
        index: u32,
    },
    /// A no-op trampoline for intrinsic core funcs (async builtins) that
    /// don't resolve to a real instance export.
    Trampoline,
    /// `canon resource.new` — allocates a handle in the resource table.
    ResourceNew {
        resource_type: u32,
    },
    /// `canon resource.rep` — retrieves the rep value for a handle.
    ResourceRep {
        resource_type: u32,
    },
    /// `canon resource.drop` — removes a handle and invokes its destructor.
    ResourceDrop {
        resource_type: u32,
    },
    /// A lowered component function that delegates to a child component
    /// instance. The trampoline calls the child's exported function.
    LoweredFunc {
        child_index: usize,
        export_name: String,
        /// String encoding from the `canon lower` that created this lowered
        /// func. Used by the fused adapter to validate string pointer alignment.
        string_encoding: crate::parse::types::StringEncoding,
    },
    /// A lowered-then-lifted core func (`canon lower` of `canon lift`).
    /// Resolves to a real core func but must trap during instantiation
    /// because the component model forbids re-entering a component
    /// during its own start sequence.
    LoweredCoreFunc {
        instance: usize,
        index: u32,
    },
}

/// Convert an `ExportKind` into a `CoreExport` tagged with the source
/// instance index and export index.
pub(crate) fn make_core_export(kind: &ExportKind, instance: usize, index: u32) -> CoreExport {
    match kind {
        ExportKind::Func => CoreExport::Func { instance, index },
        ExportKind::Global => CoreExport::Global { instance, index },
        ExportKind::Memory => CoreExport::Memory { instance, index },
        ExportKind::Table => CoreExport::Table { instance, index },
        ExportKind::Tag => CoreExport::Tag { instance, index },
    }
}

/// A live core instance — either a real instantiated module or a synthetic
/// bag of exports.
#[derive(Clone)]
pub(crate) enum CoreInstance {
    Instantiated {
        module: Rc<Module>,
        store: SharedStore,
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
    pub(super) fn resolve_export(&self, name: &str) -> Option<(ExportKind, u32)> {
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
                CoreExport::Tag { index, .. } => (ExportKind::Tag, *index),
                CoreExport::Trampoline
                | CoreExport::LoweredFunc { .. }
                | CoreExport::ResourceNew { .. }
                | CoreExport::ResourceRep { .. }
                | CoreExport::ResourceDrop { .. } => (ExportKind::Func, 0),
                CoreExport::LoweredCoreFunc { index, .. } => (ExportKind::Func, *index),
            }),
        }
    }
}

// ---------------------------------------------------------------------------
// Resolved function and component instance
// ---------------------------------------------------------------------------

/// A resolved component-level export — either a locally-resolved core func
/// or a delegation to a child component instance.
#[derive(Clone)]
pub(super) enum ResolvedExport {
    /// A function resolved to a core instance in this component instance.
    Local(ResolvedFunc),
    /// A function that lives in a child component instance, invoked by name.
    Child {
        child_index: usize,
        export_name: String,
    },
}

/// A resolved component function — points to a specific core instance and func.
#[derive(Clone)]
pub(super) struct ResolvedFunc {
    pub(super) core_instance_index: usize,
    pub(super) core_func_index: u32,
    pub(super) param_types: Vec<ComponentResultType>,
    pub(super) result_type: ComponentResultType,
    /// Resolved memory coordinates for canonical ABI string/list lifting.
    /// The usize is the core instance index that owns the memory.
    pub(super) memory_instance: Option<usize>,
    /// Core func index of the realloc function for list/string lowering.
    pub(super) realloc_func_index: Option<u32>,
}

/// An entry in the resource handle table.
#[derive(Clone, Debug)]
#[allow(dead_code)]
pub(super) struct ResourceEntry {
    /// The i32 representation value stored when the resource was created.
    pub(super) rep: i32,
    /// The resource type index (used to select the correct destructor).
    pub(super) resource_type: u32,
}

/// A shared resource handle table for a component instance.
///
/// Handles are 1-indexed. Index 0 is unused so that the first allocated
/// handle is 1, matching the Component Model spec expectations.
type SharedResourceTable = Rc<RefCell<Vec<Option<ResourceEntry>>>>;

/// A live component instance — analogous to `Store` for core modules.
#[derive(Clone)]
pub struct ComponentInstance {
    pub(super) core_instances: Vec<CoreInstance>,
    pub(super) exports: HashMap<String, ResolvedExport>,
    /// Child component instances created during instantiation.
    pub(super) child_instances: Vec<ComponentInstance>,
    /// Named sub-instance exports, keyed by export name.
    /// When a component exports an instance (e.g. `(export "nested" (instance ...))`),
    /// this maps the export name to the child `ComponentInstance` so that
    /// alias-instance-export resolution can extract the correct sub-instance.
    pub(super) exported_instances: HashMap<String, ComponentInstance>,
    /// Whether this component instance is currently being instantiated.
    /// Used to prevent re-entrance via lowered functions during start.
    pub(super) instantiating: Rc<Cell<bool>>,
    /// Shared resource handle table for this component instance.
    ///
    /// All resource types within this component share the same handle
    /// table. Handles are 1-indexed (slot 0 is a placeholder).
    pub(super) resource_table: SharedResourceTable,
}

impl Default for ComponentInstance {
    fn default() -> Self {
        ComponentInstance {
            core_instances: Vec::new(),
            exports: HashMap::new(),
            child_instances: Vec::new(),
            exported_instances: HashMap::new(),
            instantiating: Rc::new(Cell::new(false)),
            resource_table: Rc::new(RefCell::new(vec![None])),
        }
    }
}

impl ComponentInstance {
    /// Instantiate a parsed component, creating all core instances and
    /// resolving exports.
    ///
    /// # Algorithm
    ///
    /// 1. Apply outer aliases (self-aliases for top-level components).
    /// 2. For each `CoreInstanceDef`:
    ///    - `Instantiate`: parse the core module, collect imports from
    ///      the arg instances, create a `Store` with those imports, run
    ///      the start function if present.
    ///    - `FromExports`: build a synthetic instance that maps export
    ///      names to exports from other core instances.
    /// 3. Resolve component-level exports by following the chain:
    ///    component export → component func (canon lift) → core func
    ///    (alias) → core instance export → actual func index.
    pub fn instantiate(
        component: &ParsedComponent,
        types: &wasmparser::types::Types,
        features: wasmparser::WasmFeatures,
    ) -> Result<Self, String> {
        let mut component = component.clone();
        apply_self_aliases(&mut component);
        let import_instances = default_import_instances(&component);
        Self::instantiate_inner(component, import_instances, Rc::new(RefCell::new(vec![None])), types, features, 0)
    }

    /// Instantiate with positional imports (used by the Linker).
    pub(crate) fn instantiate_with_imports(
        component: &ParsedComponent,
        import_instances: Vec<ComponentInstance>,
        types: &wasmparser::types::Types,
        features: wasmparser::WasmFeatures,
    ) -> Result<Self, String> {
        let mut component = component.clone();
        apply_self_aliases(&mut component);
        Self::instantiate_inner(component, import_instances, Rc::new(RefCell::new(vec![None])), types, features, 0)
    }

    /// Inner instantiation with a shared resource table from the parent.
    ///
    /// Child components share their parent's resource table so that
    /// resource handles created by one component are visible when passed
    /// to another through imports/exports.
    fn instantiate_inner(
        component: ParsedComponent,
        import_instances: Vec<ComponentInstance>,
        resource_table: SharedResourceTable,
        types: &wasmparser::types::Types,
        features: wasmparser::WasmFeatures,
        depth: usize,
    ) -> Result<Self, String> {
        if depth > 100 {
            return Err("component instantiation depth limit exceeded".into());
        }
        let instantiating = Rc::new(Cell::new(true));
        let mut inst = ComponentInstance {
            core_instances: Vec::new(),
            exports: HashMap::new(),
            child_instances: import_instances,
            exported_instances: HashMap::new(),
            instantiating: instantiating.clone(),
            resource_table,
        };

        // Instantiate child component instances before core instances,
        // because core instances may reference modules aliased from
        // component instance exports.
        instantiate_child_components(&mut inst, &component, features, depth)?;

        for def in &component.core_instances {
            match def {
                CoreInstanceDef::Instantiate { module_index, args } => {
                    imports::instantiate_core_module(&mut inst, &component, *module_index, args)?;
                }
                CoreInstanceDef::FromExports(export_defs) => {
                    let synthetic = super::link::build_synthetic_instance(
                        &inst.core_instances,
                        &component,
                        export_defs,
                    )?;
                    inst.core_instances.push(synthetic);
                }
            }
        }

        inst.exports = super::link::resolve_component_exports(&inst.core_instances, &component, types)?;
        populate_from_exports_func_exports(&mut inst, &component, types);
        populate_exported_instances(&mut inst, &component);
        instantiating.set(false);
        Ok(inst)
    }

    /// Create a view of this instance suitable for passing as an import.
    ///
    /// Includes core instances and child instances so that resolved exports
    /// (which reference core instance indices) can still be invoked through
    /// trampolines. Also carries exported module/component bytes for alias
    /// resolution.
    pub fn export_view(&self) -> ComponentInstance {
        clone_for_export(self)
    }

    /// Check whether this instance has an export with the given name.
    pub fn has_export(&self, name: &str) -> bool {
        self.exports.contains_key(name) || self.exported_instances.contains_key(name)
    }

    /// Create a minimal view with only core instances and exports.
    ///
    /// Used when wiring func imports — the child only needs access to
    /// the source's core stores and resolved exports for trampoline
    /// creation.
    pub(super) fn core_view(&self) -> ComponentInstance {
        ComponentInstance {
            core_instances: self.core_instances.clone(),
            exports: self.exports.clone(),
            resource_table: self.resource_table.clone(),
            ..Default::default()
        }
    }

    /// Invoke a named component function with core wasm values.
    ///
    /// Convenience wrapper around `invoke_component` that wraps each
    /// `Value` in `ComponentArg::Value`.
    pub fn invoke(&mut self, name: &str, args: &[Value]) -> Result<Vec<ComponentValue>, String> {
        let component_args: Vec<ComponentArg> =
            args.iter().map(|v| ComponentArg::Value(*v)).collect();
        self.invoke_component(name, &component_args)
    }

    /// Invoke a named component function with component-level arguments.
    ///
    /// Performs canonical ABI lowering (list args → realloc + memory write),
    /// calls the underlying core function, then lifts the raw results into
    /// component-level values based on the canonical ABI result type.
    pub fn invoke_component(
        &mut self,
        name: &str,
        args: &[ComponentArg],
    ) -> Result<Vec<ComponentValue>, String> {
        let resolved = self
            .exports
            .get(name)
            .ok_or_else(|| format!("export '{}' not found", name))?
            .clone();

        match resolved {
            ResolvedExport::Child {
                child_index,
                export_name,
            } => {
                let child = self.child_instances.get_mut(child_index).ok_or_else(|| {
                    format!("child component instance {} out of bounds", child_index)
                })?;
                child.invoke_component(&export_name, args)
            }
            ResolvedExport::Local(resolved) => {
                let idx = resolved.core_instance_index;
                let func_idx = resolved.core_func_index;
                let result_type = resolved.result_type;
                let memory_instance = resolved.memory_instance;
                let realloc_func_index = resolved.realloc_func_index;

                let core_args = canonical_abi::lower_component_args(
                    args,
                    realloc_func_index,
                    &mut self.core_instances,
                    idx,
                )?;

                let instance = self
                    .core_instances
                    .get_mut(idx)
                    .ok_or_else(|| format!("core instance {} out of bounds", idx))?;
                let values = match instance {
                    CoreInstance::Instantiated { module, store } => {
                        let mut store = store.borrow_mut();
                        exec::call(module, &mut store, func_idx, &core_args)
                            .map_err(|e| format!("trap: {e}"))?
                    }
                    CoreInstance::Synthetic { .. } => {
                        return Err("cannot invoke function on synthetic instance".into());
                    }
                };
                canonical_abi::lift_results(
                    &values,
                    result_type,
                    &self.core_instances,
                    memory_instance,
                )
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Import helpers
// ---------------------------------------------------------------------------

/// Build a default (empty) `ComponentInstance` for each instance import.
///
/// Used when instantiating a component without explicit imports — each
/// instance import slot gets a placeholder so positional indexing works.
fn default_import_instances(component: &ParsedComponent) -> Vec<ComponentInstance> {
    component
        .imports()
        .iter()
        .filter(|i| i.kind == ComponentImportKind::Instance)
        .map(|_| ComponentInstance::default())
        .collect()
}

// ---------------------------------------------------------------------------
// Population helpers
// ---------------------------------------------------------------------------

/// Populate a FromExports component instance's exported sub-instances.
fn populate_from_exports_instance(
    child: &mut ComponentInstance,
    exports: &[ComponentInstanceExport],
    inst: &ComponentInstance,
) {
    for export in exports {
        if export.kind == ComponentExternalKind::Instance {
            let idx = export.index as usize;
            if idx < inst.child_instances.len() {
                let sub = clone_for_export(&inst.child_instances[idx]);
                child.exported_instances.insert(export.name.clone(), sub);
            }
        }
    }
}

/// Populate func exports on FromExports child component instances.
///
/// After component-level export resolution, iterates over each
/// `FromExports` component instance definition and copies resolved
/// func entries into the child's `exports` map.
fn populate_from_exports_func_exports(inst: &mut ComponentInstance, component: &ParsedComponent, types: &wasmparser::types::Types) {
    let import_count = component.instance_import_count as usize;
    for (def_idx, def) in component.component_instances.iter().enumerate() {
        let ComponentInstanceDef::FromExports(exports) = def else {
            continue;
        };
        let child_idx = import_count + def_idx;
        for export in exports {
            if export.kind != ComponentExternalKind::Func {
                continue;
            }
            let comp_func = component.component_funcs.get(export.index as usize);
            let Some(comp_func) = comp_func else { continue };
            let resolved = match comp_func {
                ComponentFuncDef::Lift {
                    core_func_index,
                    type_index,
                    memory_index,
                    realloc_func_index,
                } => {
                    let core_func = component.core_funcs.get(*core_func_index as usize);
                    let Some(core_func) = core_func else { continue };
                    let param_types = super::link::lookup_param_types(*type_index, types);
                    let result_type = super::link::lookup_result_type(*type_index, types);
                    match super::link::resolve_core_func_to_resolved(
                        &inst.core_instances,
                        component,
                        core_func,
                        param_types,
                        result_type,
                        *memory_index,
                        *realloc_func_index,
                        types,
                    ) {
                        Ok(resolved) => ResolvedExport::Local(resolved),
                        Err(_) => continue,
                    }
                }
                ComponentFuncDef::AliasInstanceExport {
                    instance_index,
                    name,
                } => {
                    let src = *instance_index as usize;
                    if child_idx < inst.child_instances.len()
                        && src < inst.child_instances.len()
                    {
                        let copy = inst.child_instances[src].export_view();
                        let new_idx = inst.child_instances[child_idx]
                            .child_instances
                            .len();
                        inst.child_instances[child_idx]
                            .child_instances
                            .push(copy);
                        ResolvedExport::Child {
                            child_index: new_idx,
                            export_name: name.clone(),
                        }
                    } else {
                        ResolvedExport::Child {
                            child_index: src,
                            export_name: name.clone(),
                        }
                    }
                }
            };
            if child_idx < inst.child_instances.len() {
                inst.child_instances[child_idx]
                    .exports
                    .insert(export.name.clone(), resolved);
            }
        }
        // Share the parent's core instances with the FromExports child so
        // that ResolvedExport::Local entries can find their core store.
        if child_idx < inst.child_instances.len()
            && inst.child_instances[child_idx].core_instances.is_empty()
        {
            inst.child_instances[child_idx].core_instances = inst.core_instances.clone();
        }
    }
}

/// Populate exported sub-instances from component exports.
fn populate_exported_instances(inst: &mut ComponentInstance, component: &ParsedComponent) {
    for export in &component.exports {
        if export.kind == ComponentExternalKind::Instance {
            let idx = export.index as usize;
            if idx < inst.child_instances.len() {
                let child_clone = clone_for_export(&inst.child_instances[idx]);
                inst.exported_instances
                    .insert(export.name.clone(), child_clone);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Child component instantiation
// ---------------------------------------------------------------------------

/// Instantiate all child component instances defined in the component.
fn instantiate_child_components(
    inst: &mut ComponentInstance,
    component: &ParsedComponent,
    features: wasmparser::WasmFeatures,
    depth: usize,
) -> Result<(), String> {
    for def in &component.component_instances {
        match def {
            ComponentInstanceDef::Instantiate {
                component_index,
                args,
            } => {
                let (mut inner_component, child_types) = resolve_inner_component(
                    component,
                    *component_index,
                    features,
                )?;
                apply_outer_aliases(&mut inner_component, component);

                let child = instantiate_child(
                    inst,
                    &mut inner_component,
                    args,
                    component,
                    &child_types,
                    features,
                    depth,
                )?;
                inst.child_instances.push(child);
            }
            ComponentInstanceDef::AliasInstanceExport {
                instance_index,
                name,
            } => {
                push_aliased_child_by_name(inst, *instance_index, name)?;
            }
            ComponentInstanceDef::Reexport { source_index } => {
                push_aliased_child(inst, *source_index)?;
            }
            ComponentInstanceDef::FromExports(exports) => {
                let mut child = ComponentInstance::default();
                populate_from_exports_instance(&mut child, exports, inst);
                inst.child_instances.push(child);
            }
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Instance aliasing helpers
// ---------------------------------------------------------------------------

/// Create an aliased child component instance that shares the exports
/// of the source child instance at `source_index`.
fn push_aliased_child(inst: &mut ComponentInstance, source_index: u32) -> Result<(), String> {
    let src_idx = source_index as usize;
    if src_idx >= inst.child_instances.len() {
        return Err(format!(
            "component instance {} out of bounds for alias",
            source_index
        ));
    }
    let source = &inst.child_instances[src_idx];
    let cloned = clone_for_export(source);
    inst.child_instances.push(cloned);
    Ok(())
}

/// Create an aliased child component instance by extracting a named
/// sub-instance from the source child.
fn push_aliased_child_by_name(
    inst: &mut ComponentInstance,
    source_index: u32,
    name: &str,
) -> Result<(), String> {
    let src_idx = source_index as usize;
    if src_idx >= inst.child_instances.len() {
        return Err(format!(
            "component instance {} out of bounds for alias",
            source_index
        ));
    }
    let source = &inst.child_instances[src_idx];
    if let Some(sub_instance) = source.exported_instances.get(name) {
        let cloned = clone_for_export(sub_instance);
        inst.child_instances.push(cloned);
    } else {
        let cloned = clone_for_export(source);
        inst.child_instances.push(cloned);
    }
    Ok(())
}

/// Clone a ComponentInstance for aliasing or export, copying all
/// export-related fields while resetting transient state.
pub(super) fn clone_for_export(source: &ComponentInstance) -> ComponentInstance {
    ComponentInstance {
        core_instances: source.core_instances.clone(),
        exports: source.exports.clone(),
        child_instances: source.child_instances.clone(),
        exported_instances: source.exported_instances.clone(),
        resource_table: source.resource_table.clone(),
        ..Default::default()
    }
}

// ---------------------------------------------------------------------------
// Alias resolution
// ---------------------------------------------------------------------------

/// Apply self-referencing outer aliases (count=1 at top level).
///
/// For standalone components, `count=1` outer aliases reference earlier
/// items in the same component. This copies the source bytes into the
/// placeholder slots.
fn apply_self_aliases(component: &mut ParsedComponent) {
    for alias in &component.outer_aliases.clone() {
        if alias.count != 1 {
            continue;
        }
        let src_idx = alias.index as usize;
        let dst_idx = alias.placeholder_index as usize;
        match alias.kind {
            OuterAliasKind::CoreModule => {
                if let Some(bytes) = component.core_modules.get(src_idx).cloned() {
                    if let Some(slot) = component.core_modules.get_mut(dst_idx) {
                        *slot = bytes;
                    }
                }
            }
            OuterAliasKind::Component => {
                if let Some(bytes) = component.inner_components.get(src_idx).cloned() {
                    if let Some(slot) = component.inner_components.get_mut(dst_idx) {
                        *slot = bytes;
                    }
                }
            }
            OuterAliasKind::Type | OuterAliasKind::CoreType => {}
        }
    }
}

/// Apply outer aliases from a parent component into a child.
///
/// For an outer alias with count=1, copies the source bytes from the
/// parent into the child's placeholder slot.
fn apply_outer_aliases(child: &mut ParsedComponent, parent: &ParsedComponent) {
    for alias in &child.outer_aliases.clone() {
        if alias.count != 1 {
            continue;
        }
        let src_idx = alias.index as usize;
        let dst_idx = alias.placeholder_index as usize;
        match alias.kind {
            OuterAliasKind::CoreModule => {
                if let Some(bytes) = parent.core_modules.get(src_idx) {
                    if let Some(slot) = child.core_modules.get_mut(dst_idx) {
                        *slot = bytes.clone();
                    }
                }
            }
            OuterAliasKind::Component => {
                if let Some(bytes) = parent.inner_components.get(src_idx) {
                    if let Some(slot) = child.inner_components.get_mut(dst_idx) {
                        *slot = bytes.clone();
                    }
                }
            }
            OuterAliasKind::Type | OuterAliasKind::CoreType => {}
        }
    }
}

// ---------------------------------------------------------------------------
// Instance arg wiring
// ---------------------------------------------------------------------------

/// Resolve an inner component definition by index.
///
/// Validates and parses the inner component bytes, returning both the
/// parsed structure and the child's own `Types` for type lookups.
fn resolve_inner_component(
    component: &ParsedComponent,
    component_index: u32,
    features: wasmparser::WasmFeatures,
) -> Result<(ParsedComponent, wasmparser::types::Types), String> {
    let inner_bytes = component
        .inner_components
        .get(component_index as usize)
        .filter(|b| !b.is_empty())
        .ok_or_else(|| format!("inner component {component_index} not found"))?;

    let mut validator = wasmparser::Validator::new_with_features(features);
    let (parsed, types) = crate::parse::parse_and_validate(inner_bytes, &mut validator)
        .map_err(|e| format!("{e} (component_index={component_index})"))?;
    Ok((parsed, types))
}

/// Instantiate an inner component, wiring args from the outer scope.
///
/// When `args` is empty this degenerates into a plain child instantiation.
fn instantiate_child(
    outer: &mut ComponentInstance,
    inner_component: &mut ParsedComponent,
    args: &[(String, ComponentInstanceArg)],
    outer_component: &ParsedComponent,
    types: &wasmparser::types::Types,
    features: wasmparser::WasmFeatures,
    depth: usize,
) -> Result<ComponentInstance, String> {
    let mut import_instances = Vec::new();

    if !args.is_empty() {
        wire_instance_args(
            outer,
            inner_component,
            args,
            outer_component,
            &mut import_instances,
        )?;
    } else {
        import_instances = default_import_instances(inner_component);
    }

    ComponentInstance::instantiate_inner(
        inner_component.clone(),
        import_instances,
        Rc::clone(&outer.resource_table),
        types,
        features,
        depth + 1,
    )
}

/// Wire instance args from the outer scope into an inner component.
///
/// Fills `import_instances` with child instances taken from the outer
/// scope and patches module/component slots with bytes from the outer
/// component (already resolved by the resolve phase).
fn wire_instance_args(
    outer: &mut ComponentInstance,
    inner_component: &mut ParsedComponent,
    args: &[(String, ComponentInstanceArg)],
    outer_component: &ParsedComponent,
    import_instances: &mut Vec<ComponentInstance>,
) -> Result<(), String> {
    let module_import_slot = inner_component
        .imports
        .iter()
        .filter(|i| i.kind == ComponentImportKind::Module)
        .count();
    let component_import_slot = inner_component
        .imports
        .iter()
        .filter(|i| i.kind == ComponentImportKind::Component)
        .count();

    let mut next_module_slot: usize = 0;
    let mut next_component_slot: usize = 0;

    for (_name, arg) in args {
        match arg {
            ComponentInstanceArg::Instance(idx) => {
                let src_idx = *idx as usize;
                if src_idx >= outer.child_instances.len() {
                    return Err(format!(
                        "component instance arg index {} out of bounds (have {})",
                        src_idx,
                        outer.child_instances.len()
                    ));
                }
                let taken = std::mem::take(&mut outer.child_instances[src_idx]);
                import_instances.push(taken);
            }
            ComponentInstanceArg::Module(idx) => {
                let bytes = outer_component
                    .core_modules
                    .get(*idx as usize)
                    .filter(|b| !b.is_empty())
                    .cloned();
                if let Some(bytes) = bytes {
                    if next_module_slot < module_import_slot {
                        if let Some(slot) = inner_component.core_modules.get_mut(next_module_slot) {
                            *slot = bytes;
                        }
                        next_module_slot += 1;
                    }
                }
            }
            ComponentInstanceArg::Component(idx) => {
                let bytes = outer_component
                    .inner_components
                    .get(*idx as usize)
                    .filter(|b| !b.is_empty())
                    .cloned();
                if let Some(bytes) = bytes {
                    if next_component_slot < component_import_slot {
                        if let Some(slot) = inner_component
                            .inner_components
                            .get_mut(next_component_slot)
                        {
                            *slot = bytes;
                        }
                        next_component_slot += 1;
                    }
                }
            }
            ComponentInstanceArg::Func(idx) => {
                wire_func_import(
                    outer,
                    inner_component,
                    _name,
                    *idx,
                    outer_component,
                    import_instances,
                );
            }
            ComponentInstanceArg::Type(_) => {}
        }
    }
    Ok(())
}

/// Wire a func import arg from the outer component into the inner component.
fn wire_func_import(
    outer: &mut ComponentInstance,
    inner_component: &mut ParsedComponent,
    arg_name: &str,
    outer_func_idx: u32,
    outer_component: &ParsedComponent,
    import_instances: &mut Vec<ComponentInstance>,
) {
    let inner_func_slot = inner_component.component_funcs.iter().position(|f| {
        matches!(f, ComponentFuncDef::AliasInstanceExport {
            instance_index, name
        } if *instance_index == u32::MAX && name == arg_name)
    });
    let Some(inner_slot) = inner_func_slot else {
        return;
    };

    let outer_func = outer_component.component_funcs.get(outer_func_idx as usize);
    let Some(ComponentFuncDef::AliasInstanceExport {
        instance_index,
        name,
    }) = outer_func
    else {
        return;
    };

    let src_child_idx = *instance_index as usize;
    if src_child_idx >= outer.child_instances.len() {
        return;
    }
    let child_view = outer.child_instances[src_child_idx].core_view();

    let new_child_idx = import_instances.len() as u32 + inner_component.instance_import_count;
    import_instances.push(child_view);

    inner_component.component_funcs[inner_slot] = ComponentFuncDef::AliasInstanceExport {
        instance_index: new_child_idx,
        name: name.clone(),
    };
}
