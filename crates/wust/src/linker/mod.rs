use crate::{Engine, Instance, Module, Store};

/// Resolves imports and produces instances.
pub struct Linker;

impl Linker {
    pub fn new(_engine: &Engine) -> Self {
        Self
    }

    pub fn instantiate<T>(
        &self,
        _store: &mut Store<T>,
        module: &Module,
    ) -> Result<Instance, anyhow::Error> {
        Instance::new(module)
    }
}
