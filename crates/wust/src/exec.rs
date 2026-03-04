use wust_core::{Outcome, Task};

/// An execution backend compiled for a specific module.
///
/// Implementations (JIT, interpreter, universal resumer) are tied
/// to one module and can drive any Task linked to that module.
pub trait ModuleExecutor {
    fn poll(&self, task: &mut Task) -> Outcome;
}
