//! Component model runtime.
//!
//! Implements validation, instantiation, and invocation of
//! WebAssembly components.
//!
//! - [`validate`] — wasmparser validation and wasmtime-specific restriction checks
//! - [`resolve`] — resolve phase: apply static aliases, recursively parse inner components
//! - [`link`] — alias and export resolution (core func → core instance export)
//! - [`instance`] — live state, instantiation, and export resolution

mod validate;
mod link;
mod resolve;
mod instance;
mod linker;
mod trampoline;
mod imports;

pub use crate::parse::types::{ParsedComponent, ComponentArg, ComponentImportDef, ComponentImportKind, ComponentResultType, ComponentValue};
pub(crate) use crate::parse::types::StringEncoding;
pub use instance::ComponentInstance;
pub(crate) use instance::CoreInstance;
pub use linker::Linker;

impl ParsedComponent {
    /// Whether this component declares any component-level imports.
    pub fn has_imports(&self) -> bool {
        !self.imports.is_empty()
    }

    /// The component's import declarations.
    pub fn imports(&self) -> &[ComponentImportDef] {
        &self.imports
    }

    /// Parse a component binary into a `ParsedComponent`.
    ///
    /// Validates the binary with component features enabled, then extracts
    /// the sections needed for instantiation and invocation.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        validate::validate_component(bytes)?;
        validate::validate_component_restrictions(bytes)?;
        Self::parse_sections(bytes)
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

    /// Extract sections from a component binary into a `ParsedComponent`.
    fn parse_sections(bytes: &[u8]) -> Result<Self, String> {
        let mut component = ParsedComponent {
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
            outer_aliases: Vec::new(),
            pre_resolved_inner: std::collections::HashMap::new(),
            defined_val_types: std::collections::HashMap::new(),
        };

        crate::parse::parse_component_sections(&mut component, bytes)?;
        Ok(component)
    }
}
