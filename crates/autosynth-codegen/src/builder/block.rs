use std::collections::VecDeque;
use autosynth_ir::{BlockId, Operand, VCode};

/// Mutable block under construction.
pub struct BlockBuilder {
    pub id: BlockId,
    pub vcode: VecDeque<VCode>,
    pub operands: Vec<Operand>,
    pub finalized: bool,
}

impl BlockBuilder {
    pub fn new(id: BlockId) -> Self {
        Self {
            id,
            vcode: VecDeque::new(),
            operands: Vec::new(),
            finalized: false,
        }
    }

    /// Extract successor BlockIds from branch instructions.
    pub fn successors(&self) -> Vec<BlockId> {
        self.vcode.iter().flat_map(|inst| match inst {
            VCode::Branch { target } => vec![*target],
            VCode::BrIf { block_if, block_else, .. } => vec![*block_if, *block_else],
            _ => vec![],
        }).collect()
    }
}
