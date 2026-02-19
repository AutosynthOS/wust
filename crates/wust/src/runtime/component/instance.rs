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

use super::alias;
use super::imports;
use super::types::*;

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
        string_encoding: super::types::StringEncoding,
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
    /// Core module bytes resolved from component instance export aliases.
    /// Overrides empty placeholders in `Component::core_modules`.
    pub(super) resolved_modules: HashMap<u32, Vec<u8>>,
    /// Inner component bytes resolved from component instance export aliases.
    /// Overrides empty placeholders in `Component::inner_components`.
    pub(super) resolved_components: HashMap<u32, Vec<u8>>,
    /// Exported core module bytes, keyed by export name.
    /// Allows consumers to access core module bytes from this instance.
    pub(super) exported_modules: HashMap<String, Vec<u8>>,
    /// Exported inner component bytes, keyed by export name.
    /// Allows consumers to access inner component bytes from this instance.
    pub(super) exported_components: HashMap<String, Vec<u8>>,
    /// Pre-resolved exported components, keyed by export name.
    /// When an inner component has outer aliases that reference the parent's
    /// state (e.g. module imports), the raw bytes don't capture the resolved
    /// state. This map stores the parsed Component with outer aliases already
    /// resolved, so consumers get the correct module bytes.
    pub(super) exported_pre_resolved: HashMap<String, Component>,
    /// Named sub-instance exports, keyed by export name.
    /// When a component exports an instance (e.g. `(export "nested" (instance ...))`),
    /// this maps the export name to the child `ComponentInstance` so that
    /// alias-instance-export resolution can extract the correct sub-instance.
    pub(super) exported_instances: HashMap<String, ComponentInstance>,
    /// Whether this component instance is currently being instantiated.
    /// Used to prevent re-entrance via lowered functions during start.
    pub(super) instantiating: Rc<Cell<bool>>,
    /// Pre-parsed and outer-alias-resolved components for import slots.
    /// Keyed by inner component index. When a component is passed as an arg,
    /// its outer aliases are resolved against the defining parent and the
    /// result is stored here so inner instantiation doesn't re-parse and
    /// fail to resolve outer aliases.
    pub(super) pre_resolved_components: HashMap<u32, Component>,
    /// Shared resource handle table for this component instance.
    ///
    /// All resource types within this component share the same handle
    /// table. Handles are 1-indexed (slot 0 is a placeholder).
    pub(super) resource_table: SharedResourceTable,
    /// The resolved component this instance was created from.
    /// Consumers access exported module/component bytes through
    /// `resolved.def.exports` + `resolved.def.core_modules`.
    pub(super) resolved: Rc<ResolvedComponent>,
}

impl Default for ComponentInstance {
    fn default() -> Self {
        ComponentInstance {
            core_instances: Vec::new(),
            exports: HashMap::new(),
            child_instances: Vec::new(),
            resolved_modules: HashMap::new(),
            resolved_components: HashMap::new(),
            exported_modules: HashMap::new(),
            exported_components: HashMap::new(),
            exported_pre_resolved: HashMap::new(),
            exported_instances: HashMap::new(),
            instantiating: Rc::new(Cell::new(false)),
            pre_resolved_components: HashMap::new(),
            resource_table: Rc::new(RefCell::new(vec![None])),
            resolved: Rc::new(ResolvedComponent {
                def: Component {
                    core_modules: Vec::new(),
                    core_instances: Vec::new(),
                    core_funcs: Vec::new(),
                    core_globals: Vec::new(),
                    core_memories: Vec::new(),
                    core_tables: Vec::new(),
                    core_tags: Vec::new(),
                    component_funcs: Vec::new(),
                    exports: Vec::new(),
                    component_types: Vec::new(),
                    aliased_core_modules: HashMap::new(),
                    aliased_inner_components: HashMap::new(),
                    inner_components: Vec::new(),
                    component_instances: Vec::new(),
                    instance_import_count: 0,
                    imports: Vec::new(),
                    instance_type_exports: HashMap::new(),
                    instance_type_module_constraints: HashMap::new(),
                    outer_aliases: Vec::new(),
                    pre_resolved_inner: HashMap::new(),
                    defined_val_types: HashMap::new(),
                },
                inner: Vec::new(),
            }),
        }
    }
}

impl ComponentInstance {
    /// Instantiate a parsed component, creating all core instances and
    /// resolving exports.
    ///
    /// # Algorithm
    ///
    /// 1. Resolve the component (apply aliases, parse inner components).
    /// 2. For each `CoreInstanceDef`:
    ///    - `Instantiate`: parse the core module, collect imports from
    ///      the arg instances, create a `Store` with those imports, run
    ///      the start function if present.
    ///    - `FromExports`: build a synthetic instance that maps export
    ///      names to exports from other core instances.
    /// 3. Resolve component-level exports by following the chain:
    ///    component export → component func (canon lift) → core func
    ///    (alias) → core instance export → actual func index.
    pub fn instantiate(component: &Component) -> Result<Self, String> {
        let resolved = Rc::new(super::resolve::resolve(component.clone(), &[])?);
        let import_instances = default_import_instances(component);
        Self::instantiate_from_resolved(&resolved, import_instances)
    }

    /// Instantiate from a resolved component with positional imports.
    pub(super) fn instantiate_from_resolved(
        resolved: &Rc<ResolvedComponent>,
        import_instances: Vec<ComponentInstance>,
    ) -> Result<Self, String> {
        let resource_table = Rc::new(RefCell::new(vec![None]));
        Self::instantiate_resolved_with_resource_table(
            resolved,
            import_instances,
            HashMap::new(),
            &[],
            resource_table,
        )
    }

    /// Inner instantiation with a shared resource table from the parent.
    ///
    /// Child components share their parent's resource table so that
    /// resource handles created by one component are visible when passed
    /// to another through imports/exports.
    pub(super) fn instantiate_resolved_with_resource_table(
        resolved: &Rc<ResolvedComponent>,
        import_instances: Vec<ComponentInstance>,
        pre_resolved_components: HashMap<u32, Component>,
        ancestors: &[&Component],
        resource_table: SharedResourceTable,
    ) -> Result<Self, String> {
        let component = &resolved.def;

        // Guard against infinite recursion from cyclic component instantiation.
        if ancestors.len() > 100 {
            return Err("component instantiation depth limit exceeded".into());
        }
        let instantiating = Rc::new(Cell::new(true));
        let mut inst = ComponentInstance {
            core_instances: Vec::new(),
            exports: HashMap::new(),
            child_instances: import_instances,
            resolved_modules: HashMap::new(),
            resolved_components: HashMap::new(),
            exported_modules: HashMap::new(),
            exported_components: HashMap::new(),
            exported_pre_resolved: HashMap::new(),
            exported_instances: HashMap::new(),
            instantiating: instantiating.clone(),
            pre_resolved_components,
            resource_table,
            resolved: Rc::clone(resolved),
        };

        // Resolve self-referencing outer aliases (count=1 with no parent).
        if ancestors.is_empty() {
            alias::resolve_self_aliases(&mut inst, component);
        }

        // Instantiate child component instances before core instances,
        // because core instances may reference modules aliased from
        // component instance exports.
        instantiate_child_components(&mut inst, component, resolved, ancestors)?;

        for def in &component.core_instances {
            match def {
                CoreInstanceDef::Instantiate { module_index, args } => {
                    imports::instantiate_core_module(&mut inst, component, *module_index, args)?;
                }
                CoreInstanceDef::FromExports(export_defs) => {
                    let synthetic = super::link::build_synthetic_instance(
                        &inst.core_instances,
                        component,
                        export_defs,
                    )?;
                    inst.core_instances.push(synthetic);
                }
            }
        }

        inst.exports = super::link::resolve_component_exports(&inst.core_instances, component)?;
        populate_from_exports_func_exports(&mut inst, component);
        populate_exported_bytes(&mut inst, component, ancestors);
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
fn default_import_instances(component: &Component) -> Vec<ComponentInstance> {
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

/// Resolve raw bytes for a module or component by index.
///
/// Checks the instance's resolved map first (populated from alias resolution),
/// then falls back to the component's static index space. Returns `None` if
/// the bytes are empty or not found in either source.
fn resolve_item_bytes(
    inst: &ComponentInstance,
    component: &Component,
    kind: ComponentExternalKind,
    index: u32,
) -> Option<Vec<u8>> {
    let idx = index as usize;
    let bytes = match kind {
        ComponentExternalKind::Module => inst
            .resolved_modules
            .get(&index)
            .cloned()
            .or_else(|| component.core_modules.get(idx).cloned()),
        ComponentExternalKind::Component => inst
            .resolved_components
            .get(&index)
            .cloned()
            .or_else(|| component.inner_components.get(idx).cloned()),
        _ => None,
    };
    bytes.filter(|b| !b.is_empty())
}

/// Populate a FromExports component instance's exported items.
///
/// For each export entry, looks up the item bytes in the parent component
/// and stores them in the synthetic instance's exported_modules or
/// exported_components.
fn populate_from_exports_instance(
    child: &mut ComponentInstance,
    exports: &[ComponentInstanceExport],
    component: &Component,
    inst: &ComponentInstance,
) {
    for export in exports {
        match export.kind {
            ComponentExternalKind::Module => {
                if let Some(b) = resolve_item_bytes(inst, component, export.kind, export.index) {
                    child.exported_modules.insert(export.name.clone(), b);
                }
            }
            ComponentExternalKind::Component => {
                if let Some(b) = resolve_item_bytes(inst, component, export.kind, export.index) {
                    child.exported_components.insert(export.name.clone(), b);
                }
            }
            ComponentExternalKind::Instance => {
                let idx = export.index as usize;
                if idx < inst.child_instances.len() {
                    let source = &inst.child_instances[idx];
                    child.exported_modules.extend(source.exported_modules.clone());
                    child.exported_components.extend(source.exported_components.clone());
                    child.exported_pre_resolved.extend(source.exported_pre_resolved.clone());
                    let sub = clone_for_export(source);
                    child.exported_instances.insert(export.name.clone(), sub);
                }
            }
            _ => {}
        }
    }
}

/// Populate func exports on FromExports child component instances.
///
/// After component-level export resolution, iterates over each
/// `FromExports` component instance definition and copies resolved
/// func entries into the child's `exports` map.
fn populate_from_exports_func_exports(inst: &mut ComponentInstance, component: &Component) {
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
                    let param_types = super::link::lookup_param_types(component, *type_index);
                    let result_type = super::link::lookup_result_type(component, *type_index);
                    match super::link::resolve_core_func_to_resolved(
                        &inst.core_instances,
                        component,
                        core_func,
                        param_types,
                        result_type,
                        *memory_index,
                        *realloc_func_index,
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

/// Populate exported_modules and exported_components from component exports.
fn populate_exported_bytes(
    inst: &mut ComponentInstance,
    component: &Component,
    ancestors: &[&Component],
) {
    for export in &component.exports {
        match export.kind {
            ComponentExternalKind::Module => {
                if let Some(b) = resolve_item_bytes(inst, component, export.kind, export.index) {
                    inst.exported_modules.insert(export.name.clone(), b);
                }
            }
            ComponentExternalKind::Component => {
                let bytes = resolve_item_bytes(inst, component, export.kind, export.index);
                if let Some(ref b) = bytes {
                    inst.exported_components
                        .insert(export.name.clone(), b.clone());
                }
                let idx = export.index as usize;
                if let Some(pre) = component.pre_resolved_inner.get(&(idx as u32)) {
                    inst.exported_pre_resolved
                        .insert(export.name.clone(), (**pre).clone());
                } else if let Some(ref resolved_inner) = inst.resolved.inner.get(idx) {
                    if let Some(rc) = resolved_inner {
                        // Use the resolved inner component's def as the
                        // pre-resolved Component — its outer aliases are
                        // already applied.
                        inst.exported_pre_resolved
                            .insert(export.name.clone(), rc.def.clone());
                    }
                } else if let Some(b) = bytes {
                    if let Ok(mut parsed) = super::Component::from_bytes_no_validate(&b) {
                        let mut inner_ancestors: Vec<&Component> =
                            Vec::with_capacity(ancestors.len() + 1);
                        inner_ancestors.push(component);
                        inner_ancestors.extend_from_slice(ancestors);
                        alias::resolve_outer_aliases(&mut parsed, &inner_ancestors);
                        alias::pre_resolve_inner_components(&mut parsed, &inner_ancestors);
                        inst.exported_pre_resolved
                            .insert(export.name.clone(), parsed);
                    }
                }
            }
            ComponentExternalKind::Instance => {
                let idx = export.index as usize;
                if idx < inst.child_instances.len() {
                    let child_clone = clone_for_export(&inst.child_instances[idx]);
                    inst.exported_instances
                        .insert(export.name.clone(), child_clone);
                }
            }
            _ => {}
        }
    }
}

// ---------------------------------------------------------------------------
// Child component instantiation
// ---------------------------------------------------------------------------

/// Instantiate all child component instances defined in the component.
fn instantiate_child_components(
    inst: &mut ComponentInstance,
    component: &Component,
    resolved: &Rc<ResolvedComponent>,
    ancestors: &[&Component],
) -> Result<(), String> {
    use super::Component;

    let mut inner_ancestors: Vec<&Component> = Vec::with_capacity(ancestors.len() + 1);
    inner_ancestors.push(component);
    inner_ancestors.extend_from_slice(ancestors);

    let mut parsed_inner_components: HashMap<u32, Component> = HashMap::new();

    for def in &component.component_instances {
        match def {
            ComponentInstanceDef::Instantiate {
                component_index,
                args,
            } => {
                let resolved_inner = resolved.inner.get(*component_index as usize)
                    .and_then(|opt| opt.as_ref());

                let mut inner_component = resolve_inner_component(
                    inst,
                    component,
                    *component_index,
                    &parsed_inner_components,
                    &inner_ancestors,
                )?;

                let child = instantiate_child(
                    inst,
                    &mut inner_component,
                    args,
                    component,
                    &inner_ancestors,
                    resolved_inner,
                )?;
                inst.child_instances.push(child);

                parsed_inner_components.insert(*component_index, inner_component);
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
                populate_from_exports_instance(&mut child, exports, component, inst);
                inst.child_instances.push(child);
            }
        }
    }

    // Resolve aliased core modules from component instance exports.
    alias::resolve_aliased_core_modules(inst, component, &parsed_inner_components)?;

    // Resolve aliased inner components from component instance exports.
    alias::resolve_aliased_inner_components(inst, component, &parsed_inner_components)?;

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
        exported_modules: source.exported_modules.clone(),
        exported_components: source.exported_components.clone(),
        exported_pre_resolved: source.exported_pre_resolved.clone(),
        exported_instances: source.exported_instances.clone(),
        resource_table: source.resource_table.clone(),
        resolved: Rc::clone(&source.resolved),
        ..Default::default()
    }
}

// ---------------------------------------------------------------------------
// Instance arg wiring
// ---------------------------------------------------------------------------

/// Resolve an inner component definition by index.
///
/// Tries, in order:
/// 1. Pre-resolved components (from arg wiring)
/// 2. Parent's pre-resolved inner components
/// 3. Alias-resolved pre-resolved components
/// 4. Raw bytes → parse → resolve outer aliases
fn resolve_inner_component(
    inst: &mut ComponentInstance,
    component: &Component,
    component_index: u32,
    parsed_cache: &HashMap<u32, Component>,
    ancestors: &[&Component],
) -> Result<Component, String> {
    if let Some(pre) = inst.pre_resolved_components.remove(&component_index) {
        return Ok(pre);
    }
    if let Some(pre) = component.pre_resolved_inner.get(&component_index) {
        return Ok((**pre).clone());
    }
    if let Some(pre) = alias::find_pre_resolved_from_alias(inst, component, component_index) {
        return Ok(pre);
    }
    let inner_bytes = alias::get_inner_component_bytes(
        inst,
        component,
        component_index,
        parsed_cache,
    )?;
    let mut parsed = Component::from_bytes_no_validate(&inner_bytes)
        .map_err(|e| format!("{e} (component_index={component_index})"))?;
    alias::resolve_outer_aliases(&mut parsed, ancestors);
    Ok(parsed)
}

/// Instantiate an inner component, wiring args from the outer scope.
///
/// When `args` is empty this degenerates into a plain child instantiation.
/// When a pre-resolved `ResolvedComponent` is available and no args need
/// patching, it is used directly to avoid re-resolving.
fn instantiate_child(
    outer: &mut ComponentInstance,
    inner_component: &mut Component,
    args: &[(String, ComponentInstanceArg)],
    outer_component: &Component,
    ancestors: &[&Component],
    resolved_inner: Option<&Rc<ResolvedComponent>>,
) -> Result<ComponentInstance, String> {
    let mut import_instances = Vec::new();
    let mut pre_resolved: HashMap<u32, Component> = HashMap::new();

    if !args.is_empty() {
        wire_instance_args(
            outer,
            inner_component,
            args,
            outer_component,
            ancestors,
            &mut import_instances,
            &mut pre_resolved,
        )?;
    } else {
        import_instances = default_import_instances(inner_component);
    }

    // Use the pre-resolved component if available and args didn't patch
    // anything (arg wiring mutates the component, invalidating the
    // pre-resolved version).
    let child_resolved = if args.is_empty() {
        if let Some(rc) = resolved_inner {
            Rc::clone(rc)
        } else {
            Rc::new(super::resolve::resolve(inner_component.clone(), ancestors)?)
        }
    } else {
        Rc::new(super::resolve::resolve(inner_component.clone(), ancestors)?)
    };

    ComponentInstance::instantiate_resolved_with_resource_table(
        &child_resolved,
        import_instances,
        pre_resolved,
        ancestors,
        Rc::clone(&outer.resource_table),
    )
}

/// Wire instance args from the outer scope into an inner component.
///
/// Fills `import_instances` with child instances taken from the outer
/// scope, patches module/component slots with resolved bytes, and
/// records pre-resolved components for inner slots.
fn wire_instance_args(
    outer: &mut ComponentInstance,
    inner_component: &mut Component,
    args: &[(String, ComponentInstanceArg)],
    outer_component: &Component,
    ancestors: &[&Component],
    import_instances: &mut Vec<ComponentInstance>,
    pre_resolved: &mut HashMap<u32, Component>,
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
                let bytes = resolve_arg_bytes(
                    outer,
                    *idx,
                    &outer_component.core_modules,
                    &outer.resolved_modules,
                    &outer_component.aliased_core_modules,
                    |ci| &ci.exported_modules,
                );
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
                let bytes = resolve_arg_bytes(
                    outer,
                    *idx,
                    &outer_component.inner_components,
                    &outer.resolved_components,
                    &outer_component.aliased_inner_components,
                    |ci| &ci.exported_components,
                );
                if let Some(ref bytes) = bytes {
                    if next_component_slot < component_import_slot {
                        if let Some(slot) = inner_component
                            .inner_components
                            .get_mut(next_component_slot)
                        {
                            *slot = bytes.clone();
                        }
                        if let Some(pre) = outer_component.pre_resolved_inner.get(idx) {
                            pre_resolved.insert(next_component_slot as u32, (**pre).clone());
                        } else if let Ok(mut parsed) =
                            super::Component::from_bytes_no_validate(bytes)
                        {
                            alias::resolve_outer_aliases(&mut parsed, ancestors);
                            pre_resolved.insert(next_component_slot as u32, parsed);
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

/// Resolve arg bytes from the outer scope — tries the resolved map,
/// the static index space, then aliased exports.
fn resolve_arg_bytes(
    outer: &ComponentInstance,
    idx: u32,
    static_items: &[Vec<u8>],
    resolved_map: &HashMap<u32, Vec<u8>>,
    alias_map: &HashMap<u32, (u32, String)>,
    get_exports: fn(&ComponentInstance) -> &HashMap<String, Vec<u8>>,
) -> Option<Vec<u8>> {
    resolved_map
        .get(&idx)
        .cloned()
        .or_else(|| {
            static_items
                .get(idx as usize)
                .filter(|b| !b.is_empty())
                .cloned()
        })
        .or_else(|| resolve_aliased_arg_from_exports(outer, alias_map, idx, get_exports))
}

/// Find the component_funcs slot for a func import placeholder.
pub(super) fn find_func_import_slot(funcs: &[ComponentFuncDef], name: &str) -> Option<usize> {
    funcs.iter().position(|f| {
        matches!(f, ComponentFuncDef::AliasInstanceExport {
            instance_index, name: n
        } if *instance_index == u32::MAX && n == name)
    })
}

/// Shift all component instance index references in a component by `shift`.
pub(super) fn shift_component_instance_indices(component: &mut Component, shift: u32, skip: &[usize]) {
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

/// Wire a func import arg from the outer component into the inner component.
fn wire_func_import(
    outer: &mut ComponentInstance,
    inner_component: &mut Component,
    arg_name: &str,
    outer_func_idx: u32,
    outer_component: &Component,
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

/// Resolve an aliased arg by looking up the alias map and checking the
/// child instance's exported bytes.
fn resolve_aliased_arg_from_exports(
    inst: &ComponentInstance,
    alias_map: &HashMap<u32, (u32, String)>,
    idx: u32,
    get_exports: fn(&ComponentInstance) -> &HashMap<String, Vec<u8>>,
) -> Option<Vec<u8>> {
    let (comp_inst_idx, export_name) = alias_map.get(&idx)?;
    let child = inst.child_instances.get(*comp_inst_idx as usize)?;
    let bytes = get_exports(child).get(export_name.as_str())?;
    if bytes.is_empty() { None } else { Some(bytes.clone()) }
}
