use std::{fmt::Display, ops::Deref};

use wasmparser::ValType;

use super::body::{ParsedBody, slot_size};

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
    /// Byte offset of each local (params + declared locals) from the
    /// locals base (`fp + FRAME_HEADER_SIZE`). Compact layout: i32/f32
    /// = 4 bytes, i64/f64 = 8 bytes, packed with no alignment padding.
    pub local_byte_offsets: Box<[u16]>,
    /// Cached total byte size of all locals (params + declared locals).
    pub locals_size: u16,
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

    pub fn results_size(&self) -> u16 {
        self.results.iter().map(|ty| slot_size(*ty) * 4).sum()
    }

    /// Total number of locals (params + non-param locals).
    pub fn local_count(&self) -> usize {
        self.params.len() + self.locals.len()
    }

    /// Total byte size of all locals in the compact layout.
    pub fn locals_size_bytes(&self) -> u16 {
        self.locals_size
    }

    /// Compute total byte size of params + locals.
    pub fn compute_locals_size(params: &[ValType], locals: &[ValType]) -> u16 {
        params
            .iter()
            .chain(locals.iter())
            .map(|ty| slot_size(*ty) * 4)
            .sum()
    }

    /// Compute local byte offsets from param + local types.
    pub fn compute_local_offsets(params: &[ValType], locals: &[ValType]) -> Box<[u16]> {
        let all_types = params.iter().chain(locals.iter());
        let mut offsets = Vec::with_capacity(params.len() + locals.len());
        let mut offset: u16 = 0;
        for ty in all_types {
            offsets.push(offset);
            offset += slot_size(*ty) * 4;
        }
        offsets.into_boxed_slice()
    }
}

impl Display for FuncIdx {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "fn<{}>", self.0)
    }
}
