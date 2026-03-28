use std::collections::BTreeMap;
use autosynth_ir::{BlockId, Operand, VCode};
use autosynth_regalloc::RegAlloc;

use super::BlockBuilder;
use crate::ir::{IrBlock, IrFunction, block_order};

/// Builds a function's VCode representation.
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

    pub fn emit(&mut self, inst: VCode) {
        self.current_block_mut().vcode.push_back(inst);
    }

    pub fn push_operand(&mut self, op: Operand) {
        self.current_block_mut().operands.push(op);
    }

    pub fn start_block(&mut self, id: BlockId) {
        self.blocks.entry(id).or_insert_with(|| BlockBuilder::new(id));
        self.current_block = id;
    }

    pub fn build(self) -> IrFunction {
        let successors: BTreeMap<BlockId, Vec<BlockId>> = self.blocks.iter()
            .map(|(&id, b)| (id, b.successors()))
            .collect();

        let mut predecessors: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
        for (&id, succs) in &successors {
            for &succ in succs {
                predecessors.entry(succ).or_default().push(id);
            }
        }

        let order = block_order::rpo(BlockId::Entry, &successors);

        let blocks = self.blocks.into_iter().map(|(id, b)| {
            (id, IrBlock {
                id,
                vcode: b.vcode,
                operands: b.operands,
                successors: successors.get(&id).cloned().unwrap_or_default(),
                predecessors: predecessors.remove(&id).unwrap_or_default(),
            })
        }).collect();

        IrFunction {
            regalloc: self.regalloc,
            blocks,
            block_order: order,
        }
    }

    fn current_block_mut(&mut self) -> &mut BlockBuilder {
        self.blocks.get_mut(&self.current_block).unwrap()
    }
}
