use crate::ir::function::IRFunction;

/// Collects finalized [`IRFunction`]s from one or more [`FunctionBuilder`](super::FunctionBuilder)s.
///
/// Acts as the compilation unit — the caller builds functions individually,
/// then hands the `CodeBuilder` to a backend for lowering.
pub struct CodeBuilder {
    functions: Vec<IRFunction>,
}

impl CodeBuilder {
    /// Create an empty code builder.
    pub fn new() -> Self {
        Self {
            functions: Vec::new(),
        }
    }

    /// Accept a finalized function IR produced by [`FunctionBuilder::build`](super::FunctionBuilder::build).
    pub fn push_function(&mut self, func: IRFunction) {
        self.functions.push(func);
    }

    /// Access the collected function IRs as a slice.
    pub fn functions(&self) -> &[IRFunction] {
        &self.functions
    }
}
