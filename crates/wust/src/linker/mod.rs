use crate::{Engine};

/// Resolves imports and produces instances.
pub struct Linker;

impl Linker {
    pub fn new(_engine: &Engine) -> Self {
        Self
    }

    // TODO: instantiate() needs updating once Module wraps ModuleMeta
}
