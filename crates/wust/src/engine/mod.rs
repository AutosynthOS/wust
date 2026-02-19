//! Shared configuration for wasm feature flags.
//!
//! The [`Engine`] holds feature flags that control parsing and validation.

/// Shared configuration context for wasm feature flags.
///
/// # Examples
///
/// ```ignore
/// let engine = Engine::new();
/// let component = Component::new(&engine, bytes)?;
/// let instance = component.instantiate()?;
/// ```
pub struct Engine {
    pub(crate) features: wasmparser::WasmFeatures,
}

impl Engine {
    /// Create an engine with default component model features enabled.
    pub fn new() -> Self {
        let mut features = wasmparser::WasmFeatures::default();
        features.set(wasmparser::WasmFeatures::COMPONENT_MODEL, true);
        features.set(wasmparser::WasmFeatures::CM_ASYNC, true);
        features.set(wasmparser::WasmFeatures::CM_ASYNC_STACKFUL, true);
        features.set(wasmparser::WasmFeatures::CM_ASYNC_BUILTINS, true);
        Engine { features }
    }
}
