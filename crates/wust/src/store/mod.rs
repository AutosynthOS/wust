use crate::Engine;

/// Runtime state for a WASM instance.
pub struct Store<T> {
    data: T,
}

impl<T> Store<T> {
    pub fn new(_engine: &Engine, data: T) -> Self {
        Self { data }
    }
}
