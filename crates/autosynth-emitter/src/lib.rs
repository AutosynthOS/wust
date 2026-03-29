/// Emitter trait — encodes fully-resolved VCode to machine code bytes.
///
/// All operands must be concrete (PRegs, immediates). If the emitter
/// encounters a VReg or Mem operand, that's a pipeline bug.
use autosynth_ir::{CodeCtx, Label, Operand, VCode};

/// Code output — implemented by the caller to receive emitted bytes.
pub trait CodeContext {
    type Error;

    /// Write machine code bytes to the output.
    fn emit_bytes(&mut self, bytes: &[u8]) -> Result<(), Self::Error>;

    /// Current write position (byte offset from the start).
    fn offset(&self) -> usize;

    /// Mark the current offset as the position of a label.
    fn mark_label(&mut self, label: Label);

    /// Look up the byte offset of a previously marked label.
    /// Returns `None` if the label hasn't been marked yet.
    fn label_offset(&self, label: Label) -> Option<usize>;

    /// Overwrite bytes at a specific offset. Used for patch-ups
    /// (e.g. resolving branch displacements after labels are known).
    fn write_bytes(&mut self, offset: usize, bytes: &[u8]) -> Result<(), Self::Error>;
}

/// Machine code emitter — implemented per backend.
///
/// The emitter walks the unified VCode stream. Operands precede their
/// instruction in the stream. The emitter collects operands, then
/// encodes when it hits an instruction.
pub trait Emitter {
    fn emit(
        &mut self,
        stream: &mut CodeCtx,
        ctx: &mut impl CodeContext,
    ) -> Result<(), EmitError>;
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
    /// A referenced label hasn't been marked yet.
    UnresolvedLabel,
}
