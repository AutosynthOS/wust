use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::Engine;
use crate::parse::func::{FuncIdx, ParsedFunction};
use crate::parse::parse;

static NEXT_MODULE_ID: AtomicU64 = AtomicU64::new(1);

/// Unique identifier for a compiled module.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ModuleId(u64);

/// A parsed and compiled WASM module (immutable).
#[derive(Debug, Clone)]
pub struct Module {
    id: ModuleId,
    pub(crate) funcs: Vec<ParsedFunction>,
    pub(crate) exports: HashMap<String, FuncIdx>,
}

impl Module {
    /// Parse a WAT string into a module.
    pub fn new(engine: &Engine, wat: &str) -> Result<Self, anyhow::Error> {
        let bytes = wat::parse_str(wat)?;
        Self::from_bytes(engine, &bytes)
    }

    /// Create a module from raw WASM bytes.
    pub fn from_bytes(engine: &Engine, bytes: &[u8]) -> Result<Self, anyhow::Error> {
        let parsed = parse(engine, bytes)?;
        Ok(Module {
            id: ModuleId(NEXT_MODULE_ID.fetch_add(1, Ordering::Relaxed)),
            funcs: parsed.funcs,
            exports: parsed.exports,
        })
    }

    /// This module's unique identifier.
    pub fn id(&self) -> ModuleId {
        self.id
    }

    /// Resolve an export name to a function index.
    pub fn resolve_export(&self, name: &str) -> Option<u32> {
        self.exports.get(name).map(|idx| idx.0)
    }

    pub(crate) fn get_func(&self, func_idx: FuncIdx) -> Option<&ParsedFunction> {
        self.funcs.get(func_idx.0 as usize)
    }
}
