/// Instruction selector trait and shared context types.
///
/// A selector transforms VCode + operands from an input context into
/// lowered VCode + operands in an output context. Each backend
/// (aarch64, x86, etc.) implements the [`Selector`] trait.
///
/// The same [`CodeCtx`] type is used for both input and output,
/// making passes composable — one pass's output becomes the next
/// pass's input.
use autosynth_ir::{Operand, VCode};

/// A bag of VCode instructions and operands.
///
/// Used as both input and output for selector passes. Instructions
/// and operands are parallel streams — each instruction implicitly
/// consumes and produces operands based on its arity.
pub struct CodeCtx {
    /// VCode instructions.
    pub instructions: Vec<VCode>,
    /// Operand stream, parallel to instructions.
    pub operands: Vec<Operand>,
}

impl CodeCtx {
    pub fn new() -> Self {
        Self {
            instructions: Vec::new(),
            operands: Vec::new(),
        }
    }

    pub fn from(instructions: Vec<VCode>, operands: Vec<Operand>) -> Self {
        Self { instructions, operands }
    }
}

/// Instruction selector — implemented per backend.
///
/// Consumes VCode + operands from `input`, emits lowered VCode +
/// operands into `output`. The selector drives the loop — it can
/// consume one or more input instructions per output (fusion) or
/// emit multiple outputs per input (decomposition).
///
/// Passes are composable: output becomes the next pass's input.
pub trait Selector {
    fn select(
        &mut self,
        input: &mut CodeCtx,
        output: &mut CodeCtx,
    ) -> Result<(), SelectorError>;
}

/// Errors during instruction selection.
#[derive(Debug)]
pub enum SelectorError {
    /// Unexpected end of input instructions.
    UnexpectedEnd,
    /// Unexpected end of operand stream.
    OperandUnderflow,
    /// Unhandled VCode instruction.
    Unhandled(VCode),
}
