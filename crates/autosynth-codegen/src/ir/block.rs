use autosynth_ir::{BlockId, Operand, VCode};

/// A finalized block in the IR function.
pub struct IrBlock {
    pub id: BlockId,
    pub instructions: Vec<VCode>,
    pub operands: Vec<Operand>,
    pub successors: Vec<BlockId>,
    pub predecessors: Vec<BlockId>,
}
