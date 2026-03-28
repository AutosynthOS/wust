use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use autosynth_ir::{BlockId, Operand, VCode, VRegId};
use autosynth_isa::Width;

use super::Block;

/// Builds a function's VCode representation.
///
/// Tracks VReg allocation, block structure, and the VCode + operand
/// streams. The caller (wust-codegen) manages wasm-specific regions
/// (locals, operands, fibre) and pushes VReg operands here.
pub struct FunctionBuilder {
    /// Next VRegId to allocate.
    next_vreg: u32,
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
            next_vreg: 0,
            blocks: BTreeMap::new(),
            block_order: Vec::new(),
            current_block: None,
        }
    }

    /// Allocate a new VRegId.
    pub fn alloc_vreg(&mut self) -> VRegId {
        let id = VRegId(self.next_vreg);
        self.next_vreg += 1;
        id
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
