use std::collections::HashMap;

use crate::Engine;
use crate::parse::func::{FuncIdx, ParsedFunction};
use crate::parse::parse;

/// A parsed and compiled WASM module (immutable).
#[derive(Debug, Clone)]
pub struct Module {
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
            funcs: parsed.funcs,
            exports: parsed.exports,
        })
    }

    pub(crate) fn get_func(&self, func_idx: FuncIdx) -> Option<&ParsedFunction> {
        self.funcs.get(func_idx.0 as usize)
    }

    /// Dump compiled ops and blocks for a function (for debugging/benchmarking).
    pub fn dump_func(&self, idx: usize) {
        let func = &self.funcs[idx];
        println!("=== Function {idx} ===");
        println!("params: {}, locals: {}, results: {}",
            func.param_count(), func.locals.len(), func.results.len());
        println!("\n--- ops ({}) ---", func.body.ops.len());
        for (i, op) in func.body.ops.iter().enumerate() {
            println!("  [{i:3}] 0x{:08x}  {:?}", op.raw(), op);
        }
        println!("\n--- blocks ({}) ---", func.body.blocks.len());
        for (i, block) in func.body.blocks.iter().enumerate() {
            println!("  [{i}] {:?}", block);
        }
    }

}
