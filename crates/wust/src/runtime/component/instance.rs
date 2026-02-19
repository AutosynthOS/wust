//! Live component instance state and instantiation logic.
//!
//! Contains `ComponentInstance` (analogous to `Store` for core modules)
//! and all the helpers for instantiating core modules, resolving imports,
//! and wiring up component-level exports.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::rc::Rc;

use crate::runtime::canonical_abi;
use crate::runtime::exec;
use crate::runtime::module::{ExportKind, ImportKind, Module};
use crate::runtime::store::{HostFunc, SharedStore, SharedTable, Store};
use crate::runtime::value::Value;

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
struct ResourceEntry {
    /// The i32 representation value stored when the resource was created.
    rep: i32,
    /// The resource type index (used to select the correct destructor).
    resource_type: u32,
}

/// A shared resource handle table for a component instance.
///
/// Handles are 1-indexed. Index 0 is unused so that the first allocated
/// handle is 1, matching the Component Model spec expectations.
type SharedResourceTable = Rc<RefCell<Vec<Option<ResourceEntry>>>>;

/// A live component instance — analogous to `Store` for core modules.
#[derive(Clone)]
pub struct ComponentInstance {
    core_instances: Vec<CoreInstance>,
    exports: HashMap<String, ResolvedExport>,
    /// Child component instances created during instantiation.
    child_instances: Vec<ComponentInstance>,
    /// Core module bytes resolved from component instance export aliases.
    /// Overrides empty placeholders in `Component::core_modules`.
    resolved_modules: HashMap<u32, Vec<u8>>,
    /// Inner component bytes resolved from component instance export aliases.
    /// Overrides empty placeholders in `Component::inner_components`.
    resolved_components: HashMap<u32, Vec<u8>>,
    /// Exported core module bytes, keyed by export name.
    /// Allows consumers to access core module bytes from this instance.
    exported_modules: HashMap<String, Vec<u8>>,
    /// Exported inner component bytes, keyed by export name.
    /// Allows consumers to access inner component bytes from this instance.
    exported_components: HashMap<String, Vec<u8>>,
    /// Pre-resolved exported components, keyed by export name.
    /// When an inner component has outer aliases that reference the parent's
    /// state (e.g. module imports), the raw bytes don't capture the resolved
    /// state. This map stores the parsed Component with outer aliases already
    /// resolved, so consumers get the correct module bytes.
    exported_pre_resolved: HashMap<String, Component>,
    /// Named sub-instance exports, keyed by export name.
    /// When a component exports an instance (e.g. `(export "nested" (instance ...))`),
    /// this maps the export name to the child `ComponentInstance` so that
    /// alias-instance-export resolution can extract the correct sub-instance.
    exported_instances: HashMap<String, ComponentInstance>,
    /// Whether this component instance is currently being instantiated.
    /// Used to prevent re-entrance via lowered functions during start.
    instantiating: Rc<Cell<bool>>,
    /// Pre-parsed and outer-alias-resolved components for import slots.
    /// Keyed by inner component index. When a component is passed as an arg,
    /// its outer aliases are resolved against the defining parent and the
    /// result is stored here so inner instantiation doesn't re-parse and
    /// fail to resolve outer aliases.
    pre_resolved_components: HashMap<u32, Component>,
    /// Shared resource handle table for this component instance.
    ///
    /// All resource types within this component share the same handle
    /// table. Handles are 1-indexed (slot 0 is a placeholder).
    resource_table: SharedResourceTable,
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
        }
    }
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
        if component.has_imports() {
            // Auto-supply empty instances for all instance imports.
            let import_instances: Vec<ComponentInstance> = component
                .imports()
                .iter()
                .filter(|i| i.kind == ComponentImportKind::Instance)
                .map(|_| ComponentInstance::default())
                .collect();
            Self::instantiate_inner(component, import_instances)
        } else {
            Self::instantiate_inner(component, Vec::new())
        }
    }

    /// Instantiate a component with named imports resolved from a map.
    ///
    /// For each instance import, looks up the name in the map and uses the
    /// provided instance, or falls back to an empty instance. Non-instance
    /// imports without a match produce an error.
    pub fn instantiate_with_imports(
        component: &Component,
        mut imports: HashMap<String, ComponentInstance>,
    ) -> Result<Self, String> {
        let mut import_instances = Vec::new();
        let mut func_patches: Vec<(usize, String, ComponentInstance)> = Vec::new();
        for import_def in component.imports() {
            match import_def.kind {
                ComponentImportKind::Instance => {
                    let explicitly_provided = imports.contains_key(&import_def.name);
                    let instance = imports.remove(&import_def.name).unwrap_or_default();
                    // Only validate required exports when the caller explicitly
                    // provided an instance. Unprovided instance imports default
                    // to empty instances, which is valid per the component model
                    // spec — instance types are a validation concern, not a
                    // runtime instantiation concern.
                    if explicitly_provided {
                        for required in &import_def.required_exports {
                            let has_export = instance.exports.contains_key(required)
                                || instance.exported_modules.contains_key(required)
                                || instance.exported_components.contains_key(required)
                                || instance.exported_instances.contains_key(required);
                            if !has_export {
                                return Err(format!(
                                    "import '{}': required export '{}' was not found",
                                    import_def.name, required,
                                ));
                            }
                        }
                        // Validate core module exports against type constraints.
                        validate_module_type_constraints(
                            &instance,
                            &import_def.module_type_constraints,
                        )?;
                    }
                    import_instances.push(instance);
                }
                ComponentImportKind::Func => {
                    if let Some(host_inst) = imports.remove(&import_def.name) {
                        let slot =
                            find_func_import_slot(&component.component_funcs, &import_def.name);
                        if let Some(slot_idx) = slot {
                            func_patches.push((slot_idx, import_def.name.clone(), host_inst));
                        }
                    }
                }
                _ => {}
            }
        }
        if func_patches.is_empty() {
            Self::instantiate_inner(component, import_instances)
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
            eprintln!("[FUNC-IMPORT] patched instance_import_count={}, comp_funcs len={}:", patched.instance_import_count, patched.component_funcs.len());
            for (i, f) in patched.component_funcs.iter().enumerate() {
                match f {
                    ComponentFuncDef::AliasInstanceExport { instance_index, name } => {
                        eprintln!("  comp_func[{i}] = AliasInstanceExport {{ inst={instance_index}, name={name:?} }}");
                    }
                    ComponentFuncDef::Lift { .. } => {
                        eprintln!("  comp_func[{i}] = Lift");
                    }
                }
            }
            eprintln!("[FUNC-IMPORT] import_instances.len()={}, child exports:", import_instances.len());
            for (i, inst) in import_instances.iter().enumerate() {
                eprintln!("  import[{i}]: exports={:?}, child_count={}", inst.exports.keys().collect::<Vec<_>>(), inst.child_instances.len());
            }
            Self::instantiate_inner(&patched, import_instances)
        }
    }

    /// Inner instantiation with positional instance imports.
    fn instantiate_inner(
        component: &Component,
        import_instances: Vec<ComponentInstance>,
    ) -> Result<Self, String> {
        Self::instantiate_inner_with_ancestors(component, import_instances, HashMap::new(), &[])
    }

    /// Inner instantiation with positional instance imports, pre-resolved
    /// components, and an ancestor chain for multi-level outer alias resolution.
    ///
    /// `ancestors[0]` is the grandparent (one level above this component),
    /// `ancestors[1]` is the great-grandparent, etc. The direct parent is
    /// `component` itself, which gets prepended to ancestors when resolving
    /// inner components' outer aliases.
    fn instantiate_inner_with_ancestors(
        component: &Component,
        import_instances: Vec<ComponentInstance>,
        pre_resolved_components: HashMap<u32, Component>,
        ancestors: &[&Component],
    ) -> Result<Self, String> {
        let resource_table = Rc::new(RefCell::new(vec![None]));
        Self::instantiate_inner_with_resource_table(
            component, import_instances, pre_resolved_components, ancestors, resource_table,
        )
    }

    /// Inner instantiation with a shared resource table from the parent.
    ///
    /// Child components share their parent's resource table so that
    /// resource handles created by one component are visible when passed
    /// to another through imports/exports.
    fn instantiate_inner_with_resource_table(
        component: &Component,
        import_instances: Vec<ComponentInstance>,
        pre_resolved_components: HashMap<u32, Component>,
        ancestors: &[&Component],
        resource_table: SharedResourceTable,
    ) -> Result<Self, String> {
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
        };

        // Resolve self-referencing outer aliases (count=1 with no parent).
        // This handles the pattern `(alias outer $self $item ...)` where
        // a component names itself. The alias creates a new index that
        // references an item already in the same component's index space.
        if ancestors.is_empty() {
            resolve_self_aliases(&mut inst, component);
        }

        // Instantiate child component instances before core instances,
        // because core instances may reference modules aliased from
        // component instance exports.
        instantiate_child_components(&mut inst, component, ancestors)?;

        for def in &component.core_instances {
            match def {
                CoreInstanceDef::Instantiate { module_index, args } => {
                    instantiate_core_module(&mut inst, component, *module_index, args)?;
                }
                CoreInstanceDef::FromExports(export_defs) => {
                    let synthetic = super::resolve::build_synthetic_instance(
                        &inst.core_instances,
                        component,
                        export_defs,
                    )?;
                    inst.core_instances.push(synthetic);
                }
            }
        }

        inst.exports = super::resolve::resolve_component_exports(&inst.core_instances, component)?;
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
        ComponentInstance {
            core_instances: self.core_instances.clone(),
            exports: self.exports.clone(),
            child_instances: self.child_instances.clone(),
            resolved_modules: HashMap::new(),
            resolved_components: HashMap::new(),
            exported_modules: self.exported_modules.clone(),
            exported_components: self.exported_components.clone(),
            exported_pre_resolved: self.exported_pre_resolved.clone(),
            exported_instances: self.exported_instances.clone(),
            instantiating: Rc::new(Cell::new(false)),
            pre_resolved_components: HashMap::new(),
            resource_table: self.resource_table.clone(),
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
                let idx = export.index as usize;
                let bytes = inst
                    .resolved_modules
                    .get(&export.index)
                    .cloned()
                    .or_else(|| component.core_modules.get(idx).cloned());
                if let Some(b) = bytes {
                    if !b.is_empty() {
                        child.exported_modules.insert(export.name.clone(), b);
                    }
                }
            }
            ComponentExternalKind::Component => {
                let idx = export.index as usize;
                let bytes = inst
                    .resolved_components
                    .get(&export.index)
                    .cloned()
                    .or_else(|| component.inner_components.get(idx).cloned());
                if let Some(b) = bytes {
                    if !b.is_empty() {
                        child.exported_components.insert(export.name.clone(), b);
                    }
                }
            }
            ComponentExternalKind::Instance => {
                // For instance exports in FromExports, propagate the
                // child instance's exported items and store as a named
                // sub-instance for alias-instance-export resolution.
                let idx = export.index as usize;
                if idx < inst.child_instances.len() {
                    let source = &inst.child_instances[idx];
                    child.exported_modules.extend(
                        source
                            .exported_modules
                            .iter()
                            .map(|(k, v)| (k.clone(), v.clone())),
                    );
                    child.exported_components.extend(
                        source
                            .exported_components
                            .iter()
                            .map(|(k, v)| (k.clone(), v.clone())),
                    );
                    child.exported_pre_resolved.extend(
                        source
                            .exported_pre_resolved
                            .iter()
                            .map(|(k, v)| (k.clone(), v.clone())),
                    );
                    let sub = clone_child_instance(source);
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
/// func entries into the child's `exports` map. This runs after
/// `resolve_component_exports` so that the parent's `ResolvedExport`
/// entries are available for copying.
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
                    let param_types = super::resolve::lookup_param_types(component, *type_index);
                    let result_type = super::resolve::lookup_result_type(component, *type_index);
                    match super::resolve::resolve_core_func_to_resolved(
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
///
/// For each component-level export of kind Module or Component, stores the
/// raw bytes in the instance so that consumers (via export_view) can access
/// them when aliasing core modules or inner components from this instance.
///
/// For component exports that have outer aliases, also stores a pre-resolved
/// parsed Component so consumers get the correct module bytes even when the
/// outer alias context changes.
fn populate_exported_bytes(
    inst: &mut ComponentInstance,
    component: &Component,
    ancestors: &[&Component],
) {
    for export in &component.exports {
        match export.kind {
            ComponentExternalKind::Module => {
                let idx = export.index as usize;
                // Check resolved_modules first, then component.core_modules.
                let bytes = inst
                    .resolved_modules
                    .get(&export.index)
                    .cloned()
                    .or_else(|| component.core_modules.get(idx).cloned());
                if let Some(b) = bytes {
                    if !b.is_empty() {
                        inst.exported_modules.insert(export.name.clone(), b);
                    }
                }
            }
            ComponentExternalKind::Component => {
                let idx = export.index as usize;
                let bytes = inst
                    .resolved_components
                    .get(&export.index)
                    .cloned()
                    .or_else(|| component.inner_components.get(idx).cloned());
                if let Some(ref b) = bytes {
                    if !b.is_empty() {
                        inst.exported_components
                            .insert(export.name.clone(), b.clone());
                    }
                }
                // Also store a pre-resolved Component if the inner component
                // has outer aliases. This ensures consumers get correctly
                // resolved module bytes even when re-parsed in a different
                // ancestor context.
                if let Some(pre) = component.pre_resolved_inner.get(&(idx as u32)) {
                    inst.exported_pre_resolved
                        .insert(export.name.clone(), (**pre).clone());
                } else if let Some(b) = bytes {
                    if !b.is_empty() {
                        if let Ok(mut parsed) = super::Component::from_bytes_no_validate(&b) {
                            let mut inner_ancestors: Vec<&Component> =
                                Vec::with_capacity(ancestors.len() + 1);
                            inner_ancestors.push(component);
                            inner_ancestors.extend_from_slice(ancestors);
                            resolve_outer_aliases(&mut parsed, &inner_ancestors);
                            pre_resolve_inner_components(&mut parsed, &inner_ancestors);
                            inst.exported_pre_resolved
                                .insert(export.name.clone(), parsed);
                        }
                    }
                }
            }
            ComponentExternalKind::Instance => {
                let idx = export.index as usize;
                if idx < inst.child_instances.len() {
                    let child_clone = clone_child_instance(&inst.child_instances[idx]);
                    inst.exported_instances
                        .insert(export.name.clone(), child_clone);
                }
            }
            _ => {}
        }
    }
}

// ---------------------------------------------------------------------------
// Core module instantiation
// ---------------------------------------------------------------------------

/// Instantiate all child component instances defined in the component.
///
/// Processes each `ComponentInstanceDef` in order:
/// - `Instantiate`: recursively parse and instantiate the inner component.
///   If the inner component has imports (instance args), those are satisfied
///   by moving existing child instances into the inner scope.
/// - `AliasInstanceExport`: resolve from an existing child instance's exports
///
/// Import instances are already pre-populated in `inst.child_instances`.
fn instantiate_child_components(
    inst: &mut ComponentInstance,
    component: &Component,
    ancestors: &[&Component],
) -> Result<(), String> {
    use super::Component;

    // Build the ancestor chain for inner components: this component is
    // their direct parent (index 0), followed by the existing ancestors.
    let mut inner_ancestors: Vec<&Component> = Vec::with_capacity(ancestors.len() + 1);
    inner_ancestors.push(component);
    inner_ancestors.extend_from_slice(ancestors);

    // Keep parsed inner components around so we can resolve aliased
    // core modules after all child instances are created.
    let mut parsed_inner_components: HashMap<u32, Component> = HashMap::new();

    for def in &component.component_instances {
        match def {
            ComponentInstanceDef::Instantiate {
                component_index,
                args,
            } => {
                // Check if a pre-resolved component exists (from a component
                // arg whose outer aliases were already resolved against the
                // defining parent).
                let mut inner_component = if let Some(pre) =
                    inst.pre_resolved_components.remove(component_index)
                {
                    pre
                } else if let Some(pre) = component.pre_resolved_inner.get(component_index) {
                    // Use the pre-resolved version whose outer aliases were
                    // already resolved against the correct defining context.
                    (**pre).clone()
                } else if let Some(pre) =
                    find_pre_resolved_from_alias(inst, component, *component_index)
                {
                    // The component is aliased from a child instance that has
                    // a pre-resolved version with correct outer aliases.
                    pre
                } else {
                    let inner_bytes = get_inner_component_bytes(
                        inst,
                        component,
                        *component_index,
                        &parsed_inner_components,
                    )?;
                    let mut parsed =
                        Component::from_bytes_no_validate(&inner_bytes)
                            .map_err(|e| format!("{e} (component_index={}, inner_comps={}, resolved={:?}, ancestors={})",
                                component_index,
                                component.inner_components.len(),
                                inst.resolved_components.keys().collect::<Vec<_>>(),
                                inner_ancestors.len(),
                            ))?;
                    resolve_outer_aliases(&mut parsed, &inner_ancestors);
                    parsed
                };

                let child = if inner_component.has_imports() && !args.is_empty() {
                    instantiate_with_instance_args(
                        inst,
                        &mut inner_component,
                        args,
                        component,
                        &inner_ancestors,
                    )?
                } else {
                    let import_instances: Vec<ComponentInstance> = if inner_component.has_imports()
                    {
                        inner_component
                            .imports()
                            .iter()
                            .filter(|i| i.kind == ComponentImportKind::Instance)
                            .map(|_| ComponentInstance::default())
                            .collect()
                    } else {
                        Vec::new()
                    };
                    ComponentInstance::instantiate_inner_with_resource_table(
                        &inner_component,
                        import_instances,
                        HashMap::new(),
                        &inner_ancestors,
                        Rc::clone(&inst.resource_table),
                    )?
                };
                inst.child_instances.push(child);

                // Store the parsed component for later module resolution
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
                // Synthetic component instance from explicit exports.
                // Populate exported_modules and exported_components
                // from the export entries.
                let mut child = ComponentInstance::default();
                populate_from_exports_instance(&mut child, exports, component, inst);
                inst.child_instances.push(child);
            }
        }
    }

    // Resolve aliased core modules from component instance exports.
    resolve_aliased_core_modules(inst, component, &parsed_inner_components)?;

    // Resolve aliased inner components from component instance exports.
    resolve_aliased_inner_components(inst, component, &parsed_inner_components)?;

    Ok(())
}

/// Resolve core modules that are aliased from component instance exports.
///
/// For each entry in `component.aliased_core_modules`, looks up the
/// referenced child component instance's exported_modules first, then
/// falls back to the parsed inner component's core_modules.
fn resolve_aliased_core_modules(
    inst: &mut ComponentInstance,
    component: &Component,
    parsed_inner_components: &HashMap<u32, Component>,
) -> Result<(), String> {
    for (module_idx, (comp_inst_idx, export_name)) in &component.aliased_core_modules {
        let total_idx = *comp_inst_idx as usize;

        // Check if the child instance already has exported_modules.
        if total_idx < inst.child_instances.len() {
            if let Some(bytes) = inst.child_instances[total_idx]
                .exported_modules
                .get(export_name.as_str())
            {
                if !bytes.is_empty() {
                    inst.resolved_modules.insert(*module_idx, bytes.clone());
                    continue;
                }
            }
        }

        // Fall back to parsed inner component lookup.
        let def_idx = if total_idx >= component.instance_import_count as usize {
            total_idx - component.instance_import_count as usize
        } else {
            continue;
        };

        if def_idx >= component.component_instances.len() {
            continue;
        }

        match &component.component_instances[def_idx] {
            ComponentInstanceDef::Instantiate {
                component_index, ..
            } => {
                if let Some(inner) = parsed_inner_components.get(component_index) {
                    if let Some(module_bytes) = find_exported_core_module(inner, export_name) {
                        inst.resolved_modules.insert(*module_idx, module_bytes);
                    }
                }
            }
            _ => {}
        }
    }
    Ok(())
}

/// Look up inner component bytes by index, checking multiple sources.
///
/// Checks in order: resolved_components, inner_components, on-demand
/// alias resolution from component instance exports.
fn get_inner_component_bytes(
    inst: &mut ComponentInstance,
    component: &Component,
    comp_idx: u32,
    parsed_inner_components: &HashMap<u32, Component>,
) -> Result<Vec<u8>, String> {
    // Check already-resolved components.
    if let Some(bytes) = inst.resolved_components.get(&comp_idx) {
        if !bytes.is_empty() {
            return Ok(bytes.clone());
        }
    }

    // Check the component's inner_components list.
    if let Some(bytes) = component.inner_components.get(comp_idx as usize) {
        if !bytes.is_empty() {
            return Ok(bytes.clone());
        }
    }

    // Try on-demand alias resolution.
    if let Some(bytes) =
        resolve_component_alias_on_demand(inst, component, comp_idx, parsed_inner_components)?
    {
        return Ok(bytes);
    }

    Err(format!(
        "inner component index {} out of bounds (inner_components len={}, inner_comp_empty=[{}], resolved_components={:?}, aliased={:?}, imports={:?}, comp_instances={}, outer_aliases=[{}])",
        comp_idx,
        component.inner_components.len(),
        component
            .inner_components
            .iter()
            .enumerate()
            .map(|(i, b)| format!("{}:{}", i, b.is_empty()))
            .collect::<Vec<_>>()
            .join(","),
        inst.resolved_components.keys().collect::<Vec<_>>(),
        component
            .aliased_inner_components
            .keys()
            .collect::<Vec<_>>(),
        component
            .imports
            .iter()
            .map(|i| format!("{}:{:?}", i.name, i.kind))
            .collect::<Vec<_>>(),
        component.component_instances.len(),
        component
            .outer_aliases
            .iter()
            .map(|a| format!(
                "kind={:?} count={} index={} placeholder={}",
                a.kind, a.count, a.index, a.placeholder_index
            ))
            .collect::<Vec<_>>()
            .join(", "),
    ))
}

/// Try to resolve a single aliased inner component on demand.
///
/// If the component at `comp_idx` is aliased from a component instance
/// export, look up the referenced child instance's exported_components
/// first, then fall back to parsed inner component lookup.
fn resolve_component_alias_on_demand(
    inst: &mut ComponentInstance,
    component: &Component,
    comp_idx: u32,
    parsed_inner_components: &HashMap<u32, Component>,
) -> Result<Option<Vec<u8>>, String> {
    let Some((comp_inst_idx, export_name)) = component.aliased_inner_components.get(&comp_idx)
    else {
        return Ok(None);
    };
    let total_idx = *comp_inst_idx as usize;

    // Check child instance's exported_components first.
    if total_idx < inst.child_instances.len() {
        if let Some(bytes) = inst.child_instances[total_idx]
            .exported_components
            .get(export_name.as_str())
        {
            if !bytes.is_empty() {
                inst.resolved_components.insert(comp_idx, bytes.clone());
                return Ok(Some(bytes.clone()));
            }
        }
    }

    let def_idx = if total_idx >= component.instance_import_count as usize {
        total_idx - component.instance_import_count as usize
    } else {
        return Ok(None);
    };
    if def_idx >= component.component_instances.len() {
        return Ok(None);
    }
    match &component.component_instances[def_idx] {
        ComponentInstanceDef::Instantiate {
            component_index, ..
        } => {
            if let Some(inner) = parsed_inner_components.get(component_index) {
                if let Some(comp_bytes) = find_exported_inner_component(inner, export_name) {
                    inst.resolved_components
                        .insert(comp_idx, comp_bytes.clone());
                    return Ok(Some(comp_bytes));
                }
            }
        }
        _ => {}
    }
    Ok(None)
}

/// Look up a pre-resolved Component from a child instance's export.
///
/// If the component at `comp_idx` is aliased from a child instance's export,
/// and that child has a pre-resolved version (with correct outer aliases),
/// return it. This avoids re-parsing raw bytes in a different ancestor context
/// where outer aliases would resolve incorrectly.
fn find_pre_resolved_from_alias(
    inst: &ComponentInstance,
    component: &Component,
    comp_idx: u32,
) -> Option<Component> {
    let (comp_inst_idx, export_name) = component.aliased_inner_components.get(&comp_idx)?;
    let total_idx = *comp_inst_idx as usize;
    if total_idx < inst.child_instances.len() {
        if let Some(pre) = inst.child_instances[total_idx]
            .exported_pre_resolved
            .get(export_name.as_str())
        {
            return Some(pre.clone());
        }
    }
    None
}

/// Resolve inner components that are aliased from component instance exports.
///
/// For each entry in `component.aliased_inner_components`, looks up the
/// referenced child component instance's exported_components first, then
/// falls back to the parsed inner component's inner_components.
fn resolve_aliased_inner_components(
    inst: &mut ComponentInstance,
    component: &Component,
    parsed_inner_components: &HashMap<u32, Component>,
) -> Result<(), String> {
    for (comp_idx, (comp_inst_idx, export_name)) in &component.aliased_inner_components {
        let total_idx = *comp_inst_idx as usize;

        // Check if the child instance already has exported_components.
        if total_idx < inst.child_instances.len() {
            if let Some(bytes) = inst.child_instances[total_idx]
                .exported_components
                .get(export_name.as_str())
            {
                if !bytes.is_empty() {
                    inst.resolved_components.insert(*comp_idx, bytes.clone());
                    continue;
                }
            }
        }

        // Fall back to parsed inner component lookup.
        let def_idx = if total_idx >= component.instance_import_count as usize {
            total_idx - component.instance_import_count as usize
        } else {
            continue;
        };

        if def_idx >= component.component_instances.len() {
            continue;
        }

        match &component.component_instances[def_idx] {
            ComponentInstanceDef::Instantiate {
                component_index, ..
            } => {
                if let Some(inner) = parsed_inner_components.get(component_index) {
                    if let Some(comp_bytes) = find_exported_inner_component(inner, export_name) {
                        inst.resolved_components.insert(*comp_idx, comp_bytes);
                    }
                }
            }
            _ => {}
        }
    }
    Ok(())
}

/// Find inner component bytes for a named export from a parsed component.
fn find_exported_inner_component(component: &Component, export_name: &str) -> Option<Vec<u8>> {
    for export in &component.exports {
        if export.name == export_name && export.kind == ComponentExternalKind::Component {
            return component
                .inner_components
                .get(export.index as usize)
                .cloned();
        }
    }
    None
}

/// Recursively resolve outer aliases in a component and all its inner
/// components, using the same parent context.
///
/// After resolving the top-level component's aliases, parses each inner
/// component and resolves their aliases too. This is needed when a
/// component is passed as an arg to a different parent context — its
/// outer aliases reference the original parent, not the dynamic parent.
/// Resolve outer aliases in a child component using the parent's context.
///
/// Resolve outer aliases in a child component using an ancestor chain.
///
/// `ancestors[0]` is the direct parent, `ancestors[1]` is the grandparent,
/// etc. For an outer alias with count N, we look up ancestors[N-1].
///
/// For count=1, copies from the direct parent. For count > 1, copies from
/// the appropriate ancestor, enabling deep nesting of outer aliases.
fn resolve_outer_aliases(child: &mut Component, ancestors: &[&Component]) {
    for alias in &child.outer_aliases.clone() {
        let ancestor_idx = (alias.count as usize).wrapping_sub(1);
        let Some(ancestor) = ancestors.get(ancestor_idx) else {
            continue;
        };
        let src_idx = alias.index as usize;
        let dst_idx = alias.placeholder_index as usize;
        match alias.kind {
            super::types::OuterAliasKind::CoreModule => {
                if let Some(bytes) = ancestor.core_modules.get(src_idx) {
                    if let Some(slot) = child.core_modules.get_mut(dst_idx) {
                        *slot = bytes.clone();
                    }
                }
            }
            super::types::OuterAliasKind::Component => {
                if let Some(bytes) = ancestor.inner_components.get(src_idx) {
                    if let Some(slot) = child.inner_components.get_mut(dst_idx) {
                        *slot = bytes.clone();
                    }
                }
                // Pre-resolve the obtained inner component so its outer
                // aliases are resolved against the correct (defining)
                // ancestor chain.  Without this, passing the component as
                // an arg to a different parent would re-resolve outer
                // aliases against the wrong context, causing infinite
                // recursion or incorrect component substitution.
                if let Some(pre) = ancestor.pre_resolved_inner.get(&(src_idx as u32)) {
                    child.pre_resolved_inner.insert(dst_idx as u32, pre.clone());
                } else if let Some(bytes) = ancestor.inner_components.get(src_idx) {
                    if !bytes.is_empty() {
                        if let Ok(mut parsed) = super::Component::from_bytes_no_validate(bytes) {
                            // The inner component was defined inside
                            // `ancestor`, so its count=1 aliases reference
                            // ancestor's own context = ancestors[ancestor_idx..].
                            resolve_outer_aliases(&mut parsed, &ancestors[ancestor_idx..]);
                            child
                                .pre_resolved_inner
                                .insert(dst_idx as u32, Box::new(parsed));
                        }
                    }
                }
            }
            super::types::OuterAliasKind::Type | super::types::OuterAliasKind::CoreType => {
                // Type aliases don't need runtime resolution.
            }
        }
    }
}

/// Recursively pre-resolve inner components' outer aliases.
///
/// After resolving a component's own outer aliases, its inner components may
/// still have unresolved outer aliases that reference ancestors further up the
/// chain. This function parses each inner component and resolves its outer
/// aliases using the correct ancestor chain.
fn pre_resolve_inner_components(component: &mut Component, parent_ancestors: &[&Component]) {
    for idx in 0..component.inner_components.len() {
        let bytes = &component.inner_components[idx];
        if bytes.is_empty() {
            continue;
        }
        if component.pre_resolved_inner.contains_key(&(idx as u32)) {
            continue;
        }
        let Ok(mut parsed) = super::Component::from_bytes_no_validate(bytes) else {
            continue;
        };
        if parsed.outer_aliases.is_empty() && !has_deep_outer_aliases(&parsed) {
            continue;
        }
        let mut inner_ancestors: Vec<&Component> = Vec::with_capacity(parent_ancestors.len() + 1);
        inner_ancestors.push(component);
        inner_ancestors.extend_from_slice(parent_ancestors);
        resolve_outer_aliases(&mut parsed, &inner_ancestors);
        pre_resolve_inner_components(&mut parsed, &inner_ancestors);
        component
            .pre_resolved_inner
            .insert(idx as u32, Box::new(parsed));
    }
}

/// Check whether any inner component has outer aliases that need resolution.
fn has_deep_outer_aliases(component: &Component) -> bool {
    for bytes in &component.inner_components {
        if bytes.is_empty() {
            continue;
        }
        if let Ok(parsed) = super::Component::from_bytes_no_validate(bytes) {
            if !parsed.outer_aliases.is_empty() {
                return true;
            }
            if has_deep_outer_aliases(&parsed) {
                return true;
            }
        }
    }
    false
}

/// Resolve self-referencing outer aliases in a top-level component.
///
/// When a component uses `alias outer $self $item`, it creates an outer alias
/// with count=1 that references an item in the same component. Since there is
/// no parent, we resolve these by looking up the source index in the component's
/// own index space and storing the result in `resolved_modules` / `resolved_components`.
fn resolve_self_aliases(inst: &mut ComponentInstance, component: &Component) {
    for alias in &component.outer_aliases {
        if alias.count != 0 {
            continue;
        }
        let src_idx = alias.index as usize;
        let dst_idx = alias.placeholder_index;
        match alias.kind {
            super::types::OuterAliasKind::CoreModule => {
                if let Some(bytes) = component.core_modules.get(src_idx) {
                    if !bytes.is_empty() {
                        inst.resolved_modules.insert(dst_idx, bytes.clone());
                    }
                }
            }
            super::types::OuterAliasKind::Component => {
                if let Some(bytes) = component.inner_components.get(src_idx) {
                    if !bytes.is_empty() {
                        inst.resolved_components.insert(dst_idx, bytes.clone());
                    }
                }
            }
            super::types::OuterAliasKind::Type | super::types::OuterAliasKind::CoreType => {}
        }
    }
}

/// Find the core module bytes for a named export from a parsed component.
fn find_exported_core_module(component: &Component, export_name: &str) -> Option<Vec<u8>> {
    for export in &component.exports {
        if export.name == export_name && export.kind == ComponentExternalKind::Module {
            return component.core_modules.get(export.index as usize).cloned();
        }
    }
    None
}

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
    let cloned = clone_child_instance(source);
    inst.child_instances.push(cloned);
    Ok(())
}

/// Create an aliased child component instance by extracting a named
/// sub-instance from the source child.
///
/// If the source has an `exported_instances` entry for `name`, uses that
/// sub-instance. Otherwise, falls back to cloning the source wholesale
/// (backward-compatible for simple cases where the source directly exports
/// the needed functions).
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
        let cloned = clone_child_instance(sub_instance);
        inst.child_instances.push(cloned);
    } else {
        let cloned = clone_child_instance(source);
        inst.child_instances.push(cloned);
    }
    Ok(())
}

/// Clone a ComponentInstance for use as an aliased child, copying all
/// export-related fields.
fn clone_child_instance(source: &ComponentInstance) -> ComponentInstance {
    ComponentInstance {
        core_instances: source.core_instances.clone(),
        exports: source.exports.clone(),
        child_instances: source.child_instances.clone(),
        resolved_modules: HashMap::new(),
        resolved_components: HashMap::new(),
        exported_modules: source.exported_modules.clone(),
        exported_components: source.exported_components.clone(),
        exported_pre_resolved: source.exported_pre_resolved.clone(),
        exported_instances: source.exported_instances.clone(),
        instantiating: Rc::new(Cell::new(false)),
        pre_resolved_components: HashMap::new(),
        resource_table: source.resource_table.clone(),
    }
}

/// Instantiate an inner component whose imports are satisfied by passing
/// existing child instances from the outer scope.
///
/// Instance args are moved from the outer component instance. Module and
/// component args are copied from the outer component's parsed data into
/// the inner component's index space (replacing import placeholders).
fn instantiate_with_instance_args(
    outer: &mut ComponentInstance,
    inner_component: &mut Component,
    args: &[(String, ComponentInstanceArg)],
    outer_component: &Component,
    ancestors: &[&Component],
) -> Result<ComponentInstance, String> {
    let mut import_instances = Vec::new();
    // Track which import slots we've filled for modules and components.
    let mut module_import_slot: usize = 0;
    let mut component_import_slot: usize = 0;

    // Find the placeholder slots created by imports in the inner component.
    // Module imports occupy the first N core_modules slots; component imports
    // occupy the first M inner_components slots.
    for import_def in &inner_component.imports {
        match import_def.kind {
            ComponentImportKind::Module => module_import_slot += 1,
            ComponentImportKind::Component => component_import_slot += 1,
            _ => {}
        }
    }

    // Fill import placeholder slots from the args.
    let mut next_module_slot: usize = 0;
    let mut next_component_slot: usize = 0;
    let mut pre_resolved: HashMap<u32, Component> = HashMap::new();

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
                let src_idx = *idx as usize;
                // Check resolved_modules first (for aliased core modules),
                // then component.core_modules, then try on-demand alias
                // resolution from child instance's exported_modules.
                let mut bytes = outer.resolved_modules.get(&(*idx)).cloned().or_else(|| {
                    outer_component
                        .core_modules
                        .get(src_idx)
                        .filter(|b| !b.is_empty())
                        .cloned()
                });
                if bytes.is_none() {
                    bytes = resolve_module_arg_from_exports(outer, outer_component, *idx);
                }
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
                let src_idx = *idx as usize;
                // Check resolved_components first (for aliased inner components),
                // then component.inner_components, then try on-demand alias
                // resolution from child instance's exported_components.
                let mut bytes = outer.resolved_components.get(&(*idx)).cloned().or_else(|| {
                    outer_component
                        .inner_components
                        .get(src_idx)
                        .filter(|b| !b.is_empty())
                        .cloned()
                });
                if bytes.is_none() {
                    bytes = resolve_component_arg_from_exports(outer, outer_component, *idx);
                }
                if let Some(ref bytes) = bytes {
                    if next_component_slot < component_import_slot {
                        if let Some(slot) = inner_component
                            .inner_components
                            .get_mut(next_component_slot)
                        {
                            *slot = bytes.clone();
                        }
                        // Use the pre-resolved inner component if
                        // available (outer aliases already resolved against
                        // the correct defining context).  Otherwise, parse
                        // and resolve against the current ancestor chain.
                        if let Some(pre) = outer_component.pre_resolved_inner.get(&(*idx)) {
                            pre_resolved.insert(next_component_slot as u32, (**pre).clone());
                        } else if let Ok(mut parsed) =
                            super::Component::from_bytes_no_validate(bytes)
                        {
                            resolve_outer_aliases(&mut parsed, ancestors);
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
                    &mut import_instances,
                );
            }
            ComponentInstanceArg::Type(_) => {
                // Type args don't need runtime wiring.
            }
        }
    }

    ComponentInstance::instantiate_inner_with_resource_table(
        inner_component,
        import_instances,
        pre_resolved,
        ancestors,
        Rc::clone(&outer.resource_table),
    )
}

/// Find the component_funcs slot for a func import placeholder.
///
/// Func imports are stored as `AliasInstanceExport` with `instance_index ==
/// u32::MAX`. Returns the index if found.
fn find_func_import_slot(funcs: &[ComponentFuncDef], name: &str) -> Option<usize> {
    funcs.iter().position(|f| {
        matches!(f, ComponentFuncDef::AliasInstanceExport {
            instance_index, name: n
        } if *instance_index == u32::MAX && n == name)
    })
}

/// Shift all component instance index references in a component by `shift`.
///
/// When func import instances are injected into the child_instances array
/// before the regular component instances, all existing references to
/// component instance indices must be incremented to account for the shift.
fn shift_component_instance_indices(component: &mut Component, shift: u32, skip: &[usize]) {
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
    // Shift aliased_core_modules instance indices.
    let mut new_aliased_modules = HashMap::new();
    for (k, (inst_idx, name)) in &component.aliased_core_modules {
        new_aliased_modules.insert(*k, (*inst_idx + shift, name.clone()));
    }
    component.aliased_core_modules = new_aliased_modules;
    // Shift aliased_inner_components instance indices.
    let mut new_aliased_components = HashMap::new();
    for (k, (inst_idx, name)) in &component.aliased_inner_components {
        new_aliased_components.insert(*k, (*inst_idx + shift, name.clone()));
    }
    component.aliased_inner_components = new_aliased_components;
}

/// Wire a func import arg from the outer component into the inner component.
///
/// When a component is instantiated with `(with "name" (func $src))`, we
/// resolve the outer component func to find which child instance and export
/// it references, then patch the inner component's component_funcs entry
/// so that `canon lower` can follow the alias chain to the real function.
fn wire_func_import(
    outer: &mut ComponentInstance,
    inner_component: &mut Component,
    arg_name: &str,
    outer_func_idx: u32,
    outer_component: &Component,
    import_instances: &mut Vec<ComponentInstance>,
) {
    // Step 1: Find the inner component func entry for this func import.
    // It will have instance_index == u32::MAX (placeholder from parsing).
    let inner_func_slot = inner_component.component_funcs.iter().position(|f| {
        matches!(f, ComponentFuncDef::AliasInstanceExport {
            instance_index, name
        } if *instance_index == u32::MAX && name == arg_name)
    });
    let Some(inner_slot) = inner_func_slot else {
        return;
    };

    // Step 2: Resolve the outer component func to find the source.
    let outer_func = outer_component.component_funcs.get(outer_func_idx as usize);
    let Some(ComponentFuncDef::AliasInstanceExport {
        instance_index,
        name,
    }) = outer_func
    else {
        return;
    };

    // Step 3: Get the source child instance from the outer component.
    let src_child_idx = *instance_index as usize;
    if src_child_idx >= outer.child_instances.len() {
        return;
    }
    // Build a copy of the child instance that includes its core instances
    // (needed by `make_child_instance_trampoline` to create the actual
    // trampoline closure) plus its exports.
    let src = &outer.child_instances[src_child_idx];
    let child_view = ComponentInstance {
        core_instances: src.core_instances.iter().map(|ci| ci.clone()).collect(),
        exports: src.exports.clone(),
        child_instances: Vec::new(),
        resolved_modules: HashMap::new(),
        resolved_components: HashMap::new(),
        exported_modules: HashMap::new(),
        exported_components: HashMap::new(),
        exported_pre_resolved: HashMap::new(),
        exported_instances: HashMap::new(),
        instantiating: Rc::new(Cell::new(false)),
        pre_resolved_components: HashMap::new(),
        resource_table: src.resource_table.clone(),
    };

    // Step 4: Add this child as a new import instance for the inner component.
    // The instance import count determines the child instance offset.
    let new_child_idx = import_instances.len() as u32 + inner_component.instance_import_count;
    import_instances.push(child_view);

    // Step 5: Patch the inner component's component func entry.
    inner_component.component_funcs[inner_slot] = ComponentFuncDef::AliasInstanceExport {
        instance_index: new_child_idx,
        name: name.clone(),
    };
}

/// Resolve a module arg by looking up aliased_core_modules and then checking
/// the child instance's exported_modules.
fn resolve_module_arg_from_exports(
    inst: &ComponentInstance,
    component: &Component,
    module_idx: u32,
) -> Option<Vec<u8>> {
    let (comp_inst_idx, export_name) = component.aliased_core_modules.get(&module_idx)?;
    let total_idx = *comp_inst_idx as usize;
    if total_idx < inst.child_instances.len() {
        let child = &inst.child_instances[total_idx];
        if let Some(bytes) = child.exported_modules.get(export_name.as_str()) {
            if !bytes.is_empty() {
                return Some(bytes.clone());
            }
        }
    }
    None
}

/// Resolve a component arg by looking up aliased_inner_components and then
/// checking the child instance's exported_components.
fn resolve_component_arg_from_exports(
    inst: &ComponentInstance,
    component: &Component,
    comp_idx: u32,
) -> Option<Vec<u8>> {
    let (comp_inst_idx, export_name) = component.aliased_inner_components.get(&comp_idx)?;
    let total_idx = *comp_inst_idx as usize;
    if total_idx < inst.child_instances.len() {
        let child = &inst.child_instances[total_idx];
        if let Some(bytes) = child.exported_components.get(export_name.as_str()) {
            if !bytes.is_empty() {
                return Some(bytes.clone());
            }
        }
    }
    None
}

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
    // Check resolved_modules first (for aliased core modules from
    // component instance exports), then fall back to component.core_modules.
    let module_bytes = inst
        .resolved_modules
        .get(&module_index)
        .or_else(|| component.core_modules.get(module_index as usize))
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

// ---------------------------------------------------------------------------
// Import resolution
// ---------------------------------------------------------------------------

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

/// Create a host function trampoline that returns `result_count` zero values.
///
/// Used as a fallback when no source instance is available (e.g. for
/// unmatched imports).
fn make_trampoline(result_count: usize) -> HostFunc {
    Box::new(move |_args, _mem| Ok(vec![Value::I32(0); result_count]))
}

/// Check if a synthetic instance export is a resource operation and return
/// the appropriate host function trampoline.
///
/// Returns `None` if the export is not a resource operation, in which case
/// the caller should fall back to a regular cross-instance trampoline.
fn make_resource_trampoline(
    inst: &ComponentInstance,
    source_idx: usize,
    export_name: &str,
) -> Option<HostFunc> {
    let source = inst.core_instances.get(source_idx)?;
    let CoreInstance::Synthetic { exports } = source else {
        return None;
    };
    let core_export = exports.get(export_name)?;
    match core_export {
        CoreExport::ResourceNew { resource_type } => {
            let resource_type = *resource_type;
            let table = Rc::clone(&inst.resource_table);
            Some(Box::new(move |args: &[Value], _mem: &mut [u8]| {
                let rep = match args.first() {
                    Some(Value::I32(v)) => *v,
                    _ => 0,
                };
                let mut tbl = table.borrow_mut();
                let handle = tbl.len() as i32;
                tbl.push(Some(ResourceEntry { rep, resource_type }));
                Ok(vec![Value::I32(handle)])
            }))
        }
        CoreExport::ResourceRep { .. } => {
            let table = Rc::clone(&inst.resource_table);
            Some(Box::new(move |args: &[Value], _mem: &mut [u8]| {
                let handle = match args.first() {
                    Some(Value::I32(v)) => *v as usize,
                    _ => return Err("resource.rep: expected i32 handle".into()),
                };
                let tbl = table.borrow();
                match tbl.get(handle) {
                    Some(Some(entry)) => Ok(vec![Value::I32(entry.rep)]),
                    _ => Err(format!("resource.rep: invalid handle {handle}")),
                }
            }))
        }
        CoreExport::ResourceDrop { .. } => {
            let table = Rc::clone(&inst.resource_table);
            Some(Box::new(move |args: &[Value], _mem: &mut [u8]| {
                let handle = match args.first() {
                    Some(Value::I32(v)) => *v as usize,
                    _ => return Err("resource.drop: expected i32 handle".into()),
                };
                let mut tbl = table.borrow_mut();
                match tbl.get_mut(handle) {
                    Some(slot @ Some(_)) => {
                        *slot = None;
                        Ok(vec![])
                    }
                    _ => Err(format!("resource.drop: invalid handle {handle}")),
                }
            }))
        }
        _ => None,
    }
}

/// Create a host function that calls into a source core instance.
///
/// Captures the source instance's `Rc<Module>` and `SharedStore`, then
/// on each invocation borrows the store mutably and calls `exec::call`.
/// If the source is a synthetic instance, follows the `CoreExport::Func`
/// chain to the real instance.
fn make_cross_instance_trampoline(
    inst: &ComponentInstance,
    source_idx: usize,
    export_name: &str,
    func_index: u32,
    result_count: usize,
) -> HostFunc {
    let source = &inst.core_instances[source_idx];
    match source {
        CoreInstance::Instantiated { module, store } => {
            let module = Rc::clone(module);
            let store = Rc::clone(store);
            Box::new(move |args, _mem| {
                let Ok(mut s) = store.try_borrow_mut() else {
                    return Ok(vec![Value::I32(0); result_count]);
                };
                match exec::call(&module, &mut s, func_index, args) {
                    Ok(values) => Ok(values),
                    Err(_) => Ok(vec![Value::I32(0); result_count]),
                }
            })
        }
        CoreInstance::Synthetic { exports } => {
            // Look up the specific export by name to handle synthetic
            // instances with multiple exports correctly.
            let export = exports.get(export_name);

            match export {
                Some(CoreExport::LoweredFunc {
                    child_index,
                    export_name,
                    string_encoding,
                }) => make_child_instance_trampoline(
                    inst,
                    *child_index,
                    export_name.clone(),
                    result_count,
                    *string_encoding,
                ),
                Some(CoreExport::LoweredCoreFunc { instance, index }) => {
                    make_lowered_core_trampoline(inst, *instance, *index, result_count)
                }
                Some(CoreExport::Func { instance, index }) => make_cross_instance_trampoline(
                    inst,
                    *instance,
                    export_name,
                    *index,
                    result_count,
                ),
                _ => {
                    // Fallback: try any matching export by kind.
                    let lowered = exports
                        .values()
                        .find(|e| matches!(e, CoreExport::LoweredFunc { .. }));
                    if let Some(CoreExport::LoweredFunc {
                        child_index,
                        export_name,
                        string_encoding,
                    }) = lowered
                    {
                        return make_child_instance_trampoline(
                            inst,
                            *child_index,
                            export_name.clone(),
                            result_count,
                            *string_encoding,
                        );
                    }
                    let lowered_core = exports
                        .values()
                        .find(|e| matches!(e, CoreExport::LoweredCoreFunc { .. }));
                    if let Some(CoreExport::LoweredCoreFunc { instance, index }) = lowered_core {
                        return make_lowered_core_trampoline(inst, *instance, *index, result_count);
                    }
                    let real = exports.values().find(
                        |e| matches!(e, CoreExport::Func { index, .. } if *index == func_index),
                    );
                    if let Some(CoreExport::Func { instance, index }) = real {
                        make_cross_instance_trampoline(
                            inst,
                            *instance,
                            export_name,
                            *index,
                            result_count,
                        )
                    } else {
                        make_trampoline(result_count)
                    }
                }
            }
        }
    }
}

/// Create a host function trampoline for a `canon lower` of `canon lift`.
///
/// Captures the component's `instantiating` flag and panics with
/// "cannot enter component instance" if the flag is set (i.e., the
/// component is still being instantiated). After instantiation completes,
/// the flag is cleared and subsequent calls proceed normally.
fn make_lowered_core_trampoline(
    inst: &ComponentInstance,
    source_instance: usize,
    func_index: u32,
    result_count: usize,
) -> HostFunc {
    let flag = Rc::clone(&inst.instantiating);
    let source = &inst.core_instances[source_instance];
    match source {
        CoreInstance::Instantiated { module, store } => {
            let module = Rc::clone(module);
            let store = Rc::clone(store);
            Box::new(move |args, _mem| {
                if flag.get() {
                    return Err("cannot enter component instance".into());
                }
                let Ok(mut s) = store.try_borrow_mut() else {
                    return Ok(vec![Value::I32(0); result_count]);
                };
                match exec::call(&module, &mut s, func_index, args) {
                    Ok(values) => Ok(values),
                    Err(_) => Ok(vec![Value::I32(0); result_count]),
                }
            })
        }
        CoreInstance::Synthetic { .. } => make_trampoline(result_count),
    }
}

/// Create a host function trampoline that calls through to a child
/// component instance's exported function.
///
/// This handles `canon lower` of a function imported from a child
/// component instance. The trampoline invokes the child's function
/// and returns the results.
///
/// The trampoline validates:
/// - Caller retptr/argptr alignment for compound types
/// - Callee retptr alignment for compound result types
/// - String pointer alignment based on the caller's string encoding
/// - String content bounds in the caller's memory
/// Perform a fused adapter call using memory-based parameter passing.
///
/// When a component function has too many params to pass flat, `canon lower`
/// packs them into the caller's linear memory and passes `(argptr [, retptr])`.
/// This function:
/// 1. Reads param values from caller memory at argptr
/// 2. Calls callee's realloc to allocate in callee memory
/// 3. Writes params to callee memory
/// 4. Calls the core func with callee argptr
/// 5. Reads results from callee memory at returned retptr
/// 6. Writes results to caller memory at caller retptr
#[allow(clippy::too_many_arguments)]
fn fused_memory_transfer(
    args: &[Value],
    caller_mem: &mut [u8],
    param_types: &[ComponentResultType],
    result_type: ComponentResultType,
    module: &Rc<Module>,
    store: &SharedStore,
    callee_mem_store: &Option<SharedStore>,
    func_idx: u32,
    callee_realloc_idx: Option<u32>,
    result_count: usize,
) -> Result<Vec<Value>, String> {
    let has_compound_result = matches!(result_type, ComponentResultType::Compound { .. });

    // Extract caller argptr (first arg) and optional retptr (last arg).
    let caller_argptr = match args.first() {
        Some(Value::I32(p)) => *p as u32,
        _ => return Err("expected i32 argptr in fused memory call".into()),
    };
    let caller_retptr = if has_compound_result && args.len() >= 2 {
        match args.last() {
            Some(Value::I32(p)) => Some(*p as u32),
            _ => None,
        }
    } else {
        None
    };

    // Step 1: Read param values from caller memory.
    let param_count = param_types.len();
    let param_values =
        canonical_abi::read_i32s_from_memory(caller_mem, caller_argptr, param_count)?;
    eprintln!(
        "[FUSED-MEM] caller_argptr={caller_argptr} caller_retptr={caller_retptr:?} params={param_values:?}"
    );

    // Normalize params through lift-then-lower round-trip.
    let normalized = canonical_abi::normalize_args(&param_values, param_types)?;

    // Step 2: Allocate in callee memory via realloc.
    let callee_argptr = match callee_realloc_idx {
        Some(realloc_idx) => {
            let byte_size = (param_count as u32) * 4;
            let ptr = canonical_abi::callee_realloc(module, store, realloc_idx, 4, byte_size)?;
            eprintln!("[FUSED-MEM] callee_realloc returned ptr={ptr}");
            ptr
        }
        None => return Err("callee has no realloc for argptr-mode call".into()),
    };

    // Step 3: Write params to callee memory.
    {
        let mem_store = callee_mem_store.as_ref().unwrap_or(store);
        let mut s = mem_store.borrow_mut();
        canonical_abi::write_i32s_to_memory(&mut s.memory, callee_argptr, &normalized)?;
    }

    // Step 4: Call callee core func with callee argptr.
    let callee_args = vec![Value::I32(callee_argptr as i32)];
    eprintln!("[FUSED-MEM] calling func_idx={func_idx} with callee_argptr={callee_argptr}");
    let call_results = {
        let mut s = store.borrow_mut();
        exec::call(module, &mut s, func_idx, &callee_args).map_err(|e| format!("trap: {e}"))?
    };
    eprintln!("[FUSED-MEM] call returned: {call_results:?}");

    // Step 5: If compound result, read results from callee memory.
    if has_compound_result {
        let callee_retptr = match call_results.first() {
            Some(Value::I32(p)) => *p as u32,
            _ => return Err("callee did not return retptr for compound result".into()),
        };

        // Determine result count from the compound type.
        let result_values = {
            let mem_store = callee_mem_store.as_ref().unwrap_or(store);
            let s = mem_store.borrow();
            canonical_abi::read_i32s_from_memory(&s.memory, callee_retptr, result_count)?
        };

        // Step 6: Write results to caller memory at caller retptr.
        if let Some(retptr) = caller_retptr {
            canonical_abi::write_i32s_to_memory(caller_mem, retptr, &result_values)?;
            Ok(vec![])
        } else {
            Ok(result_values)
        }
    } else {
        // Scalar result: normalize and return directly.
        canonical_abi::normalize_result(&call_results, result_type)
    }
}

fn make_child_instance_trampoline(
    inst: &ComponentInstance,
    child_index: usize,
    export_name: String,
    result_count: usize,
    caller_string_encoding: super::types::StringEncoding,
) -> HostFunc {
    // Resolve the child's export to find the actual core instance and func.
    let Some(child) = inst.child_instances.get(child_index) else {
        return make_trampoline(result_count);
    };
    let Some(resolved) = child.exports.get(&export_name) else {
        return make_trampoline(result_count);
    };
    match resolved {
        ResolvedExport::Local(func) => {
            let idx = func.core_instance_index;
            let func_idx = func.core_func_index;
            let param_types = func.param_types.clone();
            let result_type = func.result_type;
            let callee_realloc_idx = func.realloc_func_index;
            let callee_memory_instance = func.memory_instance;

            let Some(core_inst) = child.core_instances.get(idx) else {
                return make_trampoline(result_count);
            };

            // Capture callee's memory store if it differs from the func store.
            let callee_mem_store: Option<SharedStore> =
                callee_memory_instance.and_then(|mem_idx| {
                    if mem_idx == idx {
                        return None;
                    }
                    match child.core_instances.get(mem_idx)? {
                        CoreInstance::Instantiated { store, .. } => Some(Rc::clone(store)),
                        _ => None,
                    }
                });

            match core_inst {
                CoreInstance::Instantiated { module, store } => {
                    let module = Rc::clone(module);
                    let store = Rc::clone(store);
                    Box::new(move |args, caller_mem| {
                        let use_argptr =
                            canonical_abi::is_argptr_mode(args.len(), &param_types, result_type);
                        eprintln!(
                            "[FUSED] args={} param_types={} result={:?} argptr={} realloc={:?}",
                            args.len(),
                            param_types.len(),
                            result_type,
                            use_argptr,
                            callee_realloc_idx
                        );
                        if use_argptr {
                            fused_memory_transfer(
                                args,
                                caller_mem,
                                &param_types,
                                result_type,
                                &module,
                                &store,
                                &callee_mem_store,
                                func_idx,
                                callee_realloc_idx,
                                result_count,
                            )
                        } else {
                            canonical_abi::validate_fused_args(
                                args,
                                &param_types,
                                result_type,
                                caller_mem,
                                caller_string_encoding,
                                callee_realloc_idx.is_some(),
                            )?;
                            canonical_abi::validate_callee_argptr(
                                &param_types,
                                callee_realloc_idx,
                                &module,
                                &store,
                            )?;
                            let normalized = canonical_abi::normalize_args(args, &param_types)?;
                            let Ok(mut s) = store.try_borrow_mut() else {
                                return Ok(vec![Value::I32(0); result_count]);
                            };
                            match exec::call(&module, &mut s, func_idx, &normalized) {
                                Ok(values) => {
                                    canonical_abi::validate_fused_results(&values, result_type)?;
                                    canonical_abi::normalize_result(&values, result_type)
                                }
                                Err(_) => Ok(vec![Value::I32(0); result_count]),
                            }
                        }
                    })
                }
                CoreInstance::Synthetic { .. } => make_trampoline(result_count),
            }
        }
        ResolvedExport::Child {
            child_index: grandchild_idx,
            export_name: inner_name,
        } => {
            // Delegate to grandchild.
            make_child_instance_trampoline(
                child,
                *grandchild_idx,
                inner_name.clone(),
                result_count,
                caller_string_encoding,
            )
        }
    }
}

// ---------------------------------------------------------------------------
// Module type constraint validation
// ---------------------------------------------------------------------------

/// Validate that core modules exported by an instance satisfy the declared
/// module type constraints.
///
/// For each module export that has a type constraint, parses the module bytes
/// and checks:
/// 1. All expected exports exist with the correct kind and type
/// 2. All expected imports exist with the correct kind and type
fn validate_module_type_constraints(
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

/// Read a global value from a core instance.
///
/// For synthetic instances, follows the `CoreExport::Global` reference
/// to the real instantiated instance that holds the actual global value.
fn get_global_value(
    inst: &ComponentInstance,
    instance_idx: usize,
    global_idx: u32,
) -> Result<Value, String> {
    match inst.core_instances.get(instance_idx) {
        Some(CoreInstance::Instantiated { store, .. }) => {
            let store = store.borrow();
            store
                .globals
                .get(global_idx as usize)
                .copied()
                .ok_or_else(|| format!("global {} out of bounds", global_idx))
        }
        Some(CoreInstance::Synthetic { exports }) => {
            // The global_idx here is from the synthetic export resolution.
            // We need to find the export that corresponds to this global.
            // The caller looked up the export by name, got kind=Global + index.
            // For synthetic instances, we need to follow the CoreExport chain
            // to the real instance.
            //
            // Since resolve_single_import calls resolve_export which returns
            // (ExportKind::Global, index), and the index comes from the
            // CoreExport, we need to search by index.
            let real_export = exports
                .values()
                .find(|e| matches!(e, CoreExport::Global { index, .. } if *index == global_idx));
            match real_export {
                Some(CoreExport::Global { instance, index }) => {
                    get_global_value(inst, *instance, *index)
                }
                _ => Err(format!(
                    "global {} not found in synthetic instance {}",
                    global_idx, instance_idx,
                )),
            }
        }
        None => Err(format!("instance {} out of bounds", instance_idx)),
    }
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
    match inst.core_instances.get(instance_idx) {
        Some(CoreInstance::Instantiated { store, .. }) => {
            let store = store.borrow();
            store
                .tables
                .get(table_idx as usize)
                .cloned()
                .ok_or_else(|| format!("table {} out of bounds", table_idx))
        }
        Some(CoreInstance::Synthetic { exports }) => {
            let real_export = exports
                .values()
                .find(|e| matches!(e, CoreExport::Table { index, .. } if *index == table_idx));
            match real_export {
                Some(CoreExport::Table { instance, index }) => {
                    get_shared_table(inst, *instance, *index)
                }
                _ => Err(format!(
                    "table {} not found in synthetic instance {}",
                    table_idx, instance_idx,
                )),
            }
        }
        None => Err(format!("instance {} out of bounds", instance_idx)),
    }
}
