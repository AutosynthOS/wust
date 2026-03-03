use std::{fmt::Display, ops::Deref};

use wasmparser::ValType;

use super::body::ParsedBody;

/// Index into the module's function list.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct FuncIdx(u32);

impl FuncIdx {
    pub fn new(idx: u32) -> Self {
        Self(idx)
    }
}

impl Deref for FuncIdx {
    type Target = u32;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Metadata for a single function in a module.
#[derive(Debug, Clone)]
pub struct FuncMeta {
    /// params
    pub params: Box<[ValType]>,
    /// locals for the function (excluding params)
    /// note that indexes need account for params length in usage
    pub locals: Box<[ValType]>,
    /// Result types.
    pub results: Box<[ValType]>,
    /// Decoded function body (InlineOp instruction stream).
    pub body: ParsedBody,
    /// Raw WASM bytecode for the function body (code section bytes).
    /// Empty for imported functions.
    pub body_bytes: Box<[u8]>,
}

impl FuncMeta {
    pub fn params(&self) -> &[ValType] {
        &self.params
    }

    pub fn locals(&self) -> &[ValType] {
        &self.locals
    }

    pub fn param_count(&self) -> usize {
        self.params.len()
    }

    pub fn result_count(&self) -> usize {
        self.results.len()
    }

    /// Total number of locals (params + non-param locals).
    pub fn local_count(&self) -> usize {
        self.params.len() + self.locals.len()
    }
}

impl Display for FuncIdx {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "fn<{}>", self.0)
    }
}
