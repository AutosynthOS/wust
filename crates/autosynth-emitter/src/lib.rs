/// Emitter trait — encodes fully-resolved VCode to machine code bytes.
///
/// All operands must be concrete (PRegs, immediates). If the emitter
/// encounters a VReg or Mem operand, that's a pipeline bug.
use autosynth_ir::{CodeCtxUnzipper, CompileError, Label};

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
    fn label_offset(&self, label: Label) -> Option<usize>;

    /// Overwrite bytes at a specific offset.
    fn write_bytes(&mut self, offset: usize, bytes: &[u8]) -> Result<(), Self::Error>;
}

/// Machine code emitter — implemented per backend.
pub trait Emitter {
    fn emit(
        &mut self,
        stream: CodeCtxUnzipper,
        ctx: &mut impl CodeContext,
    ) -> Result<(), CompileError>;
}
