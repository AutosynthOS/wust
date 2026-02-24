use super::ParsedBody;
use wasmparser::ValType;

/// Index into the module's function list.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FuncIdx(pub(crate) u32);

/// A parsed function definition.
#[derive(Debug, Clone)]
pub struct ParsedFunction {
    /// All locals: params first, then body-declared locals.
    pub locals: Box<[ValType]>,
    pub results: Box<[ValType]>,
    /// Number of parameters (first N entries in `locals`).
    pub param_count: usize,
    /// Parsed function body.
    pub body: ParsedBody,
    /// Precomputed: `param_count * 8` (byte size of args on stack).
    pub arg_byte_count: usize,
    /// Precomputed: `(locals.len() - param_count) * 8` (bytes to zero).
    pub extra_local_bytes: usize,
    /// Precomputed: number of result values.
    pub result_count: u32,
}

impl ParsedFunction {
    pub fn param_count(&self) -> usize {
        self.param_count
    }
}
