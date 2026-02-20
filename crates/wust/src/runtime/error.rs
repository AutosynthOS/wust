/// Execution errors from the WASM interpreter.
#[derive(Debug)]
pub enum ExecError {
    Trap(String),
    NotFound(String),
}

impl ExecError {
    pub(crate) fn divide_by_zero() -> Self {
        Self::Trap("integer divide by zero".into())
    }
    pub(crate) fn integer_overflow() -> Self {
        Self::Trap("integer overflow".into())
    }
    pub(crate) fn oob_memory() -> Self {
        Self::Trap("out of bounds memory access".into())
    }
    pub(crate) fn oob_table() -> Self {
        Self::Trap("out of bounds table access".into())
    }
}

impl std::fmt::Display for ExecError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExecError::Trap(msg) => write!(f, "trap: {msg}"),
            ExecError::NotFound(msg) => write!(f, "not found: {msg}"),
        }
    }
}
