pub use wust_core::Instance;

use crate::value::{Val, WasmArgs, WasmResults};
use crate::{Module, interpreter};

/// Call an exported function via the interpreter (typed API).
pub fn call<A: WasmArgs, R: WasmResults>(
    module: &Module,
    instance: &mut Instance,
    name: &str,
    args: A,
) -> Result<R, anyhow::Error> {
    let vals = call_dynamic(module, instance, name, &args.to_vals())?;
    R::from_vals(&vals)
}

/// Call an exported function via the interpreter (dynamic API).
pub fn call_dynamic(
    module: &Module,
    instance: &mut Instance,
    name: &str,
    args: &[Val],
) -> Result<Vec<Val>, anyhow::Error> {
    let func_idx = module
        .exports
        .get(name)
        .ok_or_else(|| anyhow::anyhow!("export {name} not found"))
        .map(|idx| *idx)?;

    interpreter::call(module, instance, func_idx, args)
}
