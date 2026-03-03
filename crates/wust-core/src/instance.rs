use crate::context::Context;
use crate::fibre::FibreStack;
use crate::stack::Stack;

/// Runtime state for an instantiated WASM module.
///
/// Holds the managed wasm stack, fiber stack, and execution context.
/// The module itself is not owned here — it's passed in when needed
/// (e.g. for calls). Future additions: linear memory, tables, globals.
pub struct Instance {
    inner: Box<InstanceInner>,
}

/// All live instance state, heap-allocated so `Instance` is cheap to
/// move (single pointer).
pub struct InstanceInner {
    pub stack: Stack,
    pub fibre: FibreStack,
    pub context: Context,
}

impl Instance {
    pub fn new() -> Result<Self, anyhow::Error> {
        Ok(Self {
            inner: Box::new(InstanceInner {
                stack: Stack::new()?,
                fibre: FibreStack::new()?,
                context: Context::new(),
            }),
        })
    }
}

impl std::ops::Deref for Instance {
    type Target = InstanceInner;

    fn deref(&self) -> &InstanceInner {
        &self.inner
    }
}

impl std::ops::DerefMut for Instance {
    fn deref_mut(&mut self) -> &mut InstanceInner {
        &mut self.inner
    }
}
