use std::collections::HashMap;

use autosynth_ir::{FunctionIdx, FunctionSignature};

use crate::ir_function::IRFunction;

/// Collects finalized [`IRFunction`]s from one or more [`FunctionBuilder`](super::FunctionBuilder)s.
///
/// Acts as the compilation unit — the caller builds functions individually,
/// then hands the `CodeBuilder` to a backend for lowering. Function
/// signatures are registered upfront so that call sites can look up
/// callee parameter/result types.
pub struct CodeBuilder {
    signatures: HashMap<FunctionIdx, FunctionSignature>,
    functions: Vec<IRFunction>,
}

impl CodeBuilder {
    /// Create an empty code builder.
    pub fn new() -> Self {
        Self {
            signatures: HashMap::new(),
            functions: Vec::new(),
        }
    }

    /// Register a function signature before building its IR.
    pub fn add_signature(&mut self, idx: FunctionIdx, sig: FunctionSignature) {
        self.signatures.insert(idx, sig);
    }

    /// Look up a function's signature.
    pub fn signature(&self, idx: &FunctionIdx) -> Option<&FunctionSignature> {
        self.signatures.get(idx)
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
