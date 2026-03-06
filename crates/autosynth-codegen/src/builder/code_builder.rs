use crate::ir::function::IRFunction;

pub struct CodeBuilder {
    functions: Vec<IRFunction>,
}

impl CodeBuilder {
    pub fn new() -> Self {
        Self {
            functions: Vec::new(),
        }
    }

    /// Accept a finished function IR from a FunctionBuilder.
    pub fn push_function(&mut self, func: IRFunction) {
        self.functions.push(func);
    }

    /// Access compiled functions.
    pub fn functions(&self) -> &[IRFunction] {
        &self.functions
    }
}
