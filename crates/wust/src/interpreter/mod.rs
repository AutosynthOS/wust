use crate::{Module, Val, parse::func::FuncIdx};

mod exec_recursive;
pub(crate) use exec_recursive::Trap;

pub(crate) fn call(
    _module: &Module,
    _task: &mut wust_core::Task,
    _func_idx: FuncIdx,
    _args: &[Val],
) -> Result<Vec<Val>, anyhow::Error> {
    todo!("interpreter needs rewrite for new WasmFramePointer API")
}
