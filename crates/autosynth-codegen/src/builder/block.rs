use autosynth_ir::{BlockId, Operand, VCode};

/// Mutable block under construction.
pub struct BlockBuilder {
    pub id: BlockId,
    pub instructions: Vec<VCode>,
    pub operands: Vec<Operand>,
    pub finalized: bool,
}

impl BlockBuilder {
    pub fn new(id: BlockId) -> Self {
        Self {
            id,
            instructions: Vec::new(),
            operands: Vec::new(),
            finalized: false,
        }
    }
}

/// A finalized block in the IR function.
pub struct IrBlock {
    pub id: BlockId,
    pub instructions: Vec<VCode>,
    pub operands: Vec<Operand>,
    pub successors: Vec<BlockId>,
    pub predecessors: Vec<BlockId>,
}
