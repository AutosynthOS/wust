use std::collections::BTreeMap;
use autosynth_ir::{BlockId, Operand, VCode};
use autosynth_regalloc::RegAlloc;

use super::Block;

/// Builds a function's VCode representation.
///
/// Owns the [`RegAlloc`] — all VReg definitions go through it.
/// Tracks block structure and the VCode + operand streams per block.
pub struct FunctionBuilder {
    /// The register allocator — authority on all VRegs.
    pub regalloc: RegAlloc,
    /// All blocks, keyed by BlockId.
    blocks: BTreeMap<BlockId, Block>,
    /// Block layout order.
    block_order: Vec<BlockId>,
    /// Currently active block.
    current_block: Option<BlockId>,
}

impl FunctionBuilder {
    pub fn new() -> Self {
        Self {
            regalloc: RegAlloc::new(),
            blocks: BTreeMap::new(),
            block_order: Vec::new(),
            current_block: None,
        }
    }

    /// Emit a VCode instruction into the current block.
    pub fn emit(&mut self, inst: VCode) {
        let block = self.current_block_mut();
        block.instructions.push(inst);
    }

    /// Push an operand for the next instruction.
    pub fn push_operand(&mut self, op: Operand) {
        let block = self.current_block_mut();
        block.operands.push(op);
    }

    /// Start a new block.
    pub fn start_block(&mut self, id: BlockId) {
        if !self.blocks.contains_key(&id) {
            self.block_order.push(id);
            self.blocks.insert(id, Block::new(id));
        }
        self.current_block = Some(id);
    }

    fn current_block_mut(&mut self) -> &mut Block {
        let id = self.current_block.expect("no active block");
        self.blocks.get_mut(&id).unwrap()
    }
}
