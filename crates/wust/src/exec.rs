use wust_core::{Outcome, Task};

/// An execution backend compiled for a specific module.
///
/// Implementations (JIT, interpreter, universal resumer) are tied
/// to one module and can drive any Task linked to that module.
pub trait ModuleExecutor {
    fn poll(&self, task: &mut Task) -> Outcome;
}

/// Unpack func_idx from frame header slot 0.
pub(crate) fn frame_func_idx(header: u64) -> u32 {
    header as u32
}
