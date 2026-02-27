use crate::parse::func::FuncIdx;
use crate::stack::Stack;
use crate::value::{Val, WasmArgs, WasmResults};
use crate::{Module, Store, interpreter};

/// An instantiated WASM module.
pub struct Instance {
    pub(crate) stack: Stack,
    pub(crate) module: Module,
}

impl Instance {
    pub(crate) fn new(module: &Module) -> Result<Self, anyhow::Error> {
        Ok(Self {
            stack: Stack::new()?,
            module: module.clone(),
        })
    }

    /// Call an exported function by name (typed API).
    pub fn call<T, A: WasmArgs, R: WasmResults>(
        &mut self,
        store: &mut Store<T>,
        name: &str,
        args: A,
    ) -> Result<R, anyhow::Error> {
        let vals = self.call_dynamic(store, name, &args.to_vals())?;
        R::from_vals(&vals)
    }

    /// Call an exported function by name (dynamic API).
    pub fn call_dynamic<T>(
        &mut self,
        _store: &mut Store<T>,
        name: &str,
        args: &[Val],
    ) -> Result<Vec<Val>, anyhow::Error> {
        let func_idx = self.resolve_export_func_idx(name)?;

        interpreter::call(self, func_idx, args)
    }

    /// Get an exported global's value by name.
    pub fn get_global<T>(&self, _store: &Store<T>, _name: &str) -> Option<Val> {
        None
    }

    pub(crate) fn resolve_export_func_idx(&self, name: &str) -> Result<FuncIdx, anyhow::Error> {
        self.module
            .exports
            .get(name)
            .ok_or_else(|| anyhow::anyhow!("export {name} not found"))
            .map(|idx| *idx)
    }
}
