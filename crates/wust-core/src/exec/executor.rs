use crate::task::{Outcome, Task};

/// An execution backend compiled for a specific module.
///
/// Implementations (JIT, interpreter) are tied to one module
/// and can drive any Task linked to that module.
pub trait ModuleExecutor {
    fn poll(&self, task: &mut Task) -> Outcome;
}
