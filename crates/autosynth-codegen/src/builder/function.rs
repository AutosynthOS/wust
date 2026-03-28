use std::collections::{BTreeMap, HashSet};
use autosynth_ir::{BlockId, Operand, VCode};
use autosynth_regalloc::RegAlloc;

use super::block::{BlockBuilder, IrBlock};

/// Builds a function's VCode representation.
///
/// Owns the [`RegAlloc`] — all VReg definitions go through it.
/// Emits into the currently active [`BlockBuilder`].
pub struct FunctionBuilder {
    pub regalloc: RegAlloc,
    blocks: BTreeMap<BlockId, BlockBuilder>,
    current_block: Option<BlockId>,
}

impl FunctionBuilder {
    pub fn new() -> Self {
        Self {
            regalloc: RegAlloc::new(),
            blocks: BTreeMap::new(),
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

    /// Start or switch to a block.
    pub fn start_block(&mut self, id: BlockId) {
        self.blocks.entry(id).or_insert_with(|| BlockBuilder::new(id));
        self.current_block = Some(id);
    }

    /// Finalize — compute successors/predecessors from branch
    /// instructions, order blocks by RPO, and return the IrFunction.
    pub fn build(self) -> IrFunction {
        // Extract successors from branch instructions.
        let mut successors: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
        for (id, block) in &self.blocks {
            let mut succs = Vec::new();
            for inst in &block.instructions {
                match inst {
                    VCode::Branch { target } => succs.push(*target),
                    VCode::BrIf { block_if, block_else } => {
                        succs.push(*block_if);
                        succs.push(*block_else);
                    }
                    _ => {}
                }
            }
            successors.insert(*id, succs);
        }

        // Compute predecessors from successors.
        let mut predecessors: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
        for (&id, succs) in &successors {
            for succ in succs {
                predecessors.entry(*succ).or_default().push(id);
            }
        }

        // RPO: DFS visiting else before then so fall-throughs work.
        let block_order = rpo(&self.blocks, &successors);

        // Build IrBlocks.
        let mut ir_blocks = BTreeMap::new();
        for (id, builder) in self.blocks {
            ir_blocks.insert(id, IrBlock {
                id,
                instructions: builder.instructions,
                operands: builder.operands,
                successors: successors.remove(&id).unwrap_or_default(),
                predecessors: predecessors.remove(&id).unwrap_or_default(),
            });
        }

        IrFunction {
            regalloc: self.regalloc,
            blocks: ir_blocks,
            block_order,
        }
    }

    fn current_block_mut(&mut self) -> &mut BlockBuilder {
        let id = self.current_block.expect("no active block");
        self.blocks.get_mut(&id).unwrap()
    }
}

/// A completed function — finalized blocks in RPO + regalloc state.
pub struct IrFunction {
    pub regalloc: RegAlloc,
    pub blocks: BTreeMap<BlockId, IrBlock>,
    pub block_order: Vec<BlockId>,
}

/// Compute reverse postorder of the block graph.
fn rpo(
    blocks: &BTreeMap<BlockId, BlockBuilder>,
    successors: &BTreeMap<BlockId, Vec<BlockId>>,
) -> Vec<BlockId> {
    let mut visited = HashSet::new();
    let mut postorder = Vec::new();

    if let Some(&entry) = blocks.keys().next() {
        dfs(entry, successors, &mut visited, &mut postorder);
    }

    postorder.reverse();
    postorder
}

fn dfs(
    id: BlockId,
    successors: &BTreeMap<BlockId, Vec<BlockId>>,
    visited: &mut HashSet<BlockId>,
    postorder: &mut Vec<BlockId>,
) {
    if !visited.insert(id) {
        return;
    }
    if let Some(succs) = successors.get(&id) {
        for &succ in succs.iter().rev() {
            dfs(succ, successors, visited, postorder);
        }
    }
    postorder.push(id);
}
