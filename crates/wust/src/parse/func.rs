use super::ParsedBody;
use wasmparser::ValType;

/// Index into the module's function list.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FuncIdx(pub(crate) u32);

/// A parsed function definition.
#[derive(Debug, Clone)]
pub struct ParsedFunction {
    pub locals: Box<[ValType]>,
    pub results: Box<[ValType]>,
    /// Parsed function body.
    pub body: ParsedBody,
}

impl ParsedFunction {
    pub fn get_size_of_locals(&self) -> usize {
        self.locals.iter().map(get_size_of_value).sum()
    }
    pub fn get_size_of_results(&self) -> usize {
        self.results.iter().map(get_size_of_value).sum()
    }
}

fn get_size_of_value(value: &ValType) -> usize {
    match value {
        ValType::I32 => 4,
        ValType::I64 => 8,
        ValType::F32 => 4,
        ValType::F64 => 8,
        ValType::V128 => 16,
        ValType::Ref(..) => 8,
    }
}
