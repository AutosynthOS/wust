/// Emitter trait — encodes fully-resolved VCode to machine code bytes.
///
/// All operands must be concrete (PRegs, immediates). If the emitter
/// encounters a VReg or Mem operand, that's a pipeline bug.
use autosynth_ir::{Operand, VCode};

/// Code output — implemented by the caller to receive emitted bytes.
pub trait CodeContext {
    type Error;

    /// Write machine code bytes to the output.
    fn emit_bytes(&mut self, bytes: &[u8]) -> Result<(), Self::Error>;
}

/// Machine code emitter — implemented per backend.
///
/// The emitter consumes operands from the iterator as needed per
/// instruction. It knows the arity of each VCode instruction.
pub trait Emitter {
    fn emit(
        &mut self,
        inst: &VCode,
        operands: &mut impl Iterator<Item = Operand>,
        ctx: &mut impl CodeContext,
    ) -> Result<(), EmitError>;
}

impl CodeContext for Vec<u8> {
    type Error = core::convert::Infallible;
    fn emit_bytes(&mut self, bytes: &[u8]) -> Result<(), Self::Error> {
        self.extend_from_slice(bytes);
        Ok(())
    }
}

#[derive(Debug)]
pub enum EmitError {
    /// An operand was not fully resolved (VReg or Mem still present).
    UnresolvedOperand,
    /// Ran out of operands.
    OperandUnderflow,
    /// An immediate value is out of encodable range.
    ImmediateOutOfRange,
    /// Unhandled VCode instruction.
    Unhandled,
}
