/// Emitter trait — encodes fully-resolved VCode to machine code bytes.
///
/// All operands must be concrete (PRegs, immediates). If the emitter
/// encounters a VReg or Mem operand, that's a pipeline bug.
///
/// The emitter is stateful — it tracks labels for branch targets and
/// patches them after all code has been emitted.
use autosynth_ir::{BlockId, Operand, VCode};

/// Machine code emitter — implemented per backend.
pub trait Emitter {
    /// Emit one VCode instruction with its operands.
    ///
    /// All operands must be fully resolved (PRegs, immediates).
    /// Returns an error if any VReg or Mem operands remain.
    fn emit(
        &mut self,
        inst: &VCode,
        operands: &[Operand],
    ) -> Result<(), EmitError>;

    /// Bind a label at the current code offset.
    /// Called before emitting a block's instructions.
    fn bind_label(&mut self, block: BlockId);

    /// Patch all branch/call offsets after all code has been emitted.
    fn patch_labels(&mut self) -> Result<(), EmitError>;

    /// The emitted machine code bytes.
    fn code(&self) -> &[u8];
}

#[derive(Debug)]
pub enum EmitError {
    /// An operand was not fully resolved (VReg or Mem still present).
    UnresolvedOperand(Operand),
    /// A branch target label was never bound.
    UnboundLabel(BlockId),
    /// An immediate value is out of encodable range.
    ImmediateOutOfRange,
}
