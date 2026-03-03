mod linear_memory;

use std::ops::Deref;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::module::ParsedModule;
use crate::task::Task;
use crate::value::Val;
use linear_memory::LinearMemory;

static NEXT_INSTANCE_ID: AtomicU64 = AtomicU64::new(1);

/// Unique identifier for an instantiated WASM module.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InstanceIdx(u64);

impl InstanceIdx {
    fn next() -> Self {
        Self(NEXT_INSTANCE_ID.fetch_add(1, Ordering::Relaxed))
    }
}

impl Deref for InstanceIdx {
    type Target = u64;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Runtime state for an instantiated WASM module.
///
/// Linked to a specific module via `Arc<ModuleMeta>`. Holds shared
/// module-level state (memory, globals, tables — not yet implemented).
/// Tasks are created via `setup_call`.
pub struct Instance {
    pub id: InstanceIdx,
    module: ParsedModule,
    // we might need to store diffrent memory types
    // e.g. shared, linear, external
    _memory: LinearMemory,
}

impl Instance {
    pub fn new(module: &ParsedModule) -> Self {
        Self {
            id: InstanceIdx::next(),
            module: module.clone(),
            _memory: LinearMemory::new(),
        }
    }

    /// Prepare a function call: resolve the export, write the frame
    /// header and args, and return a Task ready to be polled.
    pub fn setup_call(&self, name: &str, args: &[Val]) -> Result<Task, anyhow::Error> {
        Task::setup(&self, name, args)
    }

    pub fn module(&self) -> &ParsedModule {
        &self.module
    }
}
