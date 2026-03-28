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
    current_block: BlockId,
}

impl FunctionBuilder {
    pub fn new() -> Self {
        let entry = BlockId::Entry;
        let mut blocks = BTreeMap::new();
        blocks.insert(entry, BlockBuilder::new(entry));
        Self {
            regalloc: RegAlloc::new(),
            blocks,
            current_block: entry,
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
        self.current_block = id;
    }

    /// Finalize — compute control flow edges, order blocks by RPO,
    /// and return the IrFunction.
    pub fn build(self) -> IrFunction {
        let successors = extract_successors(&self.blocks);
        let predecessors = compute_predecessors(&successors);
        let block_order = rpo(&self.blocks, &successors);
        let blocks = finalize_blocks(self.blocks, successors, predecessors);

        IrFunction {
            regalloc: self.regalloc,
            blocks,
            block_order,
        }
    }

    fn current_block_mut(&mut self) -> &mut BlockBuilder {
        self.blocks.get_mut(&self.current_block).unwrap()
    }
}

/// A completed function — finalized blocks in RPO + regalloc state.
pub struct IrFunction {
    pub regalloc: RegAlloc,
    pub blocks: BTreeMap<BlockId, IrBlock>,
    pub block_order: Vec<BlockId>,
}

fn extract_successors(blocks: &BTreeMap<BlockId, BlockBuilder>) -> BTreeMap<BlockId, Vec<BlockId>> {
    blocks.iter().map(|(&id, block)| {
        let succs = block.instructions.iter().flat_map(|inst| match inst {
            VCode::Branch { target } => vec![*target],
            VCode::BrIf { block_if, block_else } => vec![*block_if, *block_else],
            _ => vec![],
        }).collect();
        (id, succs)
    }).collect()
}

fn compute_predecessors(successors: &BTreeMap<BlockId, Vec<BlockId>>) -> BTreeMap<BlockId, Vec<BlockId>> {
    let mut predecessors: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
    for (&id, succs) in successors {
        for &succ in succs {
            predecessors.entry(succ).or_default().push(id);
        }
    }
    predecessors
}

fn finalize_blocks(
    builders: BTreeMap<BlockId, BlockBuilder>,
    mut successors: BTreeMap<BlockId, Vec<BlockId>>,
    mut predecessors: BTreeMap<BlockId, Vec<BlockId>>,
) -> BTreeMap<BlockId, IrBlock> {
    builders.into_iter().map(|(id, b)| {
        (id, IrBlock {
            id,
            instructions: b.instructions,
            operands: b.operands,
            successors: successors.remove(&id).unwrap_or_default(),
            predecessors: predecessors.remove(&id).unwrap_or_default(),
        })
    }).collect()
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
