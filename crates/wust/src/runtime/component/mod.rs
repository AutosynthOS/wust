//! Component model runtime.
//!
//! Implements parsing, validation, instantiation, and invocation of
//! WebAssembly components.
//!
//! - [`types`] — parsed component definitions (immutable "code" side)
//! - [`validate`] — wasmparser validation and wasmtime-specific restriction checks
//! - [`parse`] — binary section parsing
//! - [`instance`] — live state, instantiation, and export resolution

mod types;
mod validate;
mod parse;
mod resolve;
mod instance;

pub use types::{Component, ComponentArg, ComponentImportDef, ComponentImportKind, ComponentResultType, ComponentValue};
pub(crate) use types::StringEncoding;
pub use instance::ComponentInstance;
pub(crate) use instance::CoreInstance;

/// Resolve outer aliases that reference items in the same component.
///
/// For standalone components, `count=1` outer aliases reference earlier
/// items in the same component. This copies the source bytes into the
/// placeholder slots.
fn resolve_self_outer_aliases(component: &mut Component) {
    for alias in &component.outer_aliases.clone() {
        if alias.count != 1 {
            continue;
        }
        let src_idx = alias.index as usize;
        let dst_idx = alias.placeholder_index as usize;
        match alias.kind {
            types::OuterAliasKind::CoreModule => {
                if let Some(bytes) = component.core_modules.get(src_idx).cloned() {
                    if let Some(slot) = component.core_modules.get_mut(dst_idx) {
                        *slot = bytes;
                    }
                }
            }
            types::OuterAliasKind::Component => {
                if let Some(bytes) = component.inner_components.get(src_idx).cloned() {
                    if let Some(slot) = component.inner_components.get_mut(dst_idx) {
                        *slot = bytes;
                    }
                }
            }
            types::OuterAliasKind::Type | types::OuterAliasKind::CoreType => {}
        }
    }
}

impl Component {
    /// Whether this component declares any component-level imports.
    pub fn has_imports(&self) -> bool {
        !self.imports.is_empty()
    }

    /// The component's import declarations.
    pub fn imports(&self) -> &[ComponentImportDef] {
        &self.imports
    }

    /// Parse a component binary into a `Component`.
    ///
    /// Validates the binary with component features enabled, then extracts
    /// the sections needed for instantiation and invocation.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        validate::validate_component(bytes)?;
        validate::validate_component_restrictions(bytes)?;
        let mut component = Self::parse_sections(bytes)?;
        // Resolve self-referencing outer aliases (count=1 at the top level).
        resolve_self_outer_aliases(&mut component);
        Ok(component)
    }

    /// Parse a component binary without validation.
    ///
    /// Used for inner components that were already validated as part of
    /// their parent component. Standalone validation would reject outer
    /// aliases since the parent context is not available.
    pub(crate) fn from_bytes_no_validate(bytes: &[u8]) -> Result<Self, String> {
        if bytes.is_empty() {
            return Err("cannot parse empty bytes as component".into());
        }
        Self::parse_sections(bytes)
    }

    /// Extract sections from a component binary into a `Component`.
    fn parse_sections(bytes: &[u8]) -> Result<Self, String> {
        let mut component = Component {
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
            aliased_core_modules: std::collections::HashMap::new(),
            aliased_inner_components: std::collections::HashMap::new(),
            inner_components: Vec::new(),
            component_instances: Vec::new(),
            instance_import_count: 0,
            imports: Vec::new(),
            instance_type_exports: std::collections::HashMap::new(),
            instance_type_module_constraints: std::collections::HashMap::new(),
            outer_aliases: Vec::new(),
            pre_resolved_inner: std::collections::HashMap::new(),
            defined_val_types: std::collections::HashMap::new(),
        };

        parse::parse_component_sections(&mut component, bytes)?;
        Ok(component)
    }
}
