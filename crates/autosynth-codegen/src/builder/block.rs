use alloc::vec::Vec;
use autosynth_ir::{BlockId, Operand, VCode, VRegId};

/// A basic block in the VCode pipeline.
///
/// Each block contains a sequence of VCode instructions and tracks
/// the operand state at entry (inherited from predecessors) and
/// exit (after all instructions have been processed).
///
/// At branch points, the exit operand state is snapshot'd for each
/// successor. At merge points, differing VRegIds in the same
/// position create phi nodes.
pub struct Block {
    pub id: BlockId,
    /// VCode instructions in this block.
    pub instructions: Vec<VCode>,
    /// Operands consumed/produced by instructions in this block.
    /// Parallel to instructions — each instruction's operands are
    /// appended here in order.
    pub operands: Vec<Operand>,
    /// Successor block IDs.
    pub successors: Vec<BlockId>,
    /// Whether the block has been finalized (has a terminator).
    pub finalized: bool,
}

impl Block {
    pub fn new(id: BlockId) -> Self {
        Self {
            id,
            instructions: Vec::new(),
            operands: Vec::new(),
            successors: Vec::new(),
            finalized: false,
        }
    }
}
