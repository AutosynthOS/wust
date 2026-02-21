//! User-facing component type, ready for instantiation.
//!
//! Created via [`Component::new`], which validates and parses a
//! component binary in a single pass.

use crate::engine::Engine;
use crate::parse::types::{ComponentImportDef, ParsedComponent};
use crate::runtime::component::ComponentInstance;

/// A validated and parsed component, ready for instantiation.
///
/// Holds both the parsed structure (`ParsedComponent`) and the
/// fully resolved type information (`Types`) from wasmparser's
/// validator.
pub struct Component {
    pub(crate) parsed: ParsedComponent,
    pub(crate) types: wasmparser::types::Types,
    pub(crate) features: wasmparser::WasmFeatures,
}

impl Component {
    /// Validate and parse a component binary.
    pub fn new(engine: &Engine, bytes: &[u8]) -> Result<Self, String> {
        let mut validator = wasmparser::Validator::new_with_features(engine.features);
        let (parsed, types) =
            crate::parse::parse_and_validate(bytes, &mut validator).map_err(|e| e.to_string())?;
        Ok(Component { parsed, types, features: engine.features })
    }

    /// The component's import declarations.
    pub fn imports(&self) -> &[ComponentImportDef] {
        &self.parsed.imports
    }

    /// Whether this component declares any component-level imports.
    pub fn has_imports(&self) -> bool {
        !self.parsed.imports.is_empty()
    }

    /// Instantiate this component without any imports.
    pub fn instantiate(&self) -> Result<ComponentInstance, String> {
        ComponentInstance::instantiate(&self.parsed, &self.types, self.features)
    }
}
