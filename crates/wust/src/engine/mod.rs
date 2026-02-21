use wasmparser::{Validator, WasmFeatures};

/// Shared compilation configuration.
pub struct Engine {
    features: WasmFeatures,
}

impl Engine {
    /// Create a new validator with the engine's features.
    pub fn new_validator(&self) -> Validator {
        Validator::new_with_features(self.features)
    }
}

impl Default for Engine {
    fn default() -> Self {
        let mut features = WasmFeatures::default();
        features.set(WasmFeatures::COMPONENT_MODEL, true);
        features.set(WasmFeatures::CM_ASYNC, true);
        features.set(WasmFeatures::CM_ASYNC_STACKFUL, true);
        features.set(WasmFeatures::CM_ASYNC_BUILTINS, true);
        Self { features }
    }
}
