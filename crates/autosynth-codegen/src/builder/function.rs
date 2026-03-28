use std::collections::BTreeMap;
use autosynth_ir::{BlockId, Operand, VCode, VInit, VReg};
use autosynth_regalloc::RegAlloc;

use super::{BlockBuilder, VRefId, VRefSource, VRegOrRef};
use crate::ir::{IrBlock, IrFunction, block_order};

/// Builds a function's VCode representation.
pub struct FunctionBuilder {
    pub regalloc: RegAlloc,
    blocks: BTreeMap<BlockId, BlockBuilder>,
    current_block: BlockId,
    /// Ref table — builder-local indirections for block-inherited values.
    refs: Vec<VRefSource>,
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
            refs: Vec::new(),
        }
    }

    pub fn emit(&mut self, inst: VCode) {
        self.current_block_mut().vcode.push_back(inst);
    }

    pub fn push_operand(&mut self, val: impl Into<VRegOrRef>) {
        self.current_block_mut().operands.push(val.into());
    }

    pub fn current_block_id(&self) -> BlockId {
        self.current_block
    }

    pub fn current_block(&self) -> &BlockBuilder {
        self.blocks.get(&self.current_block).unwrap()
    }

    pub fn current_block_mut(&mut self) -> &mut BlockBuilder {
        self.blocks.get_mut(&self.current_block).unwrap()
    }

    pub fn start_block(&mut self, id: BlockId) {
        self.blocks.entry(id).or_insert_with(|| BlockBuilder::new(id));
        self.current_block = id;
    }

    // --- Ref table ---

    pub fn alloc_ref(&mut self, source: VRefSource) -> VRefId {
        let id = VRefId(self.refs.len() as u32);
        self.refs.push(source);
        id
    }

    pub fn ref_source(&self, id: VRefId) -> &VRefSource {
        &self.refs[id.0 as usize]
    }

    // --- Build ---

    pub fn build(mut self) -> IrFunction {
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

        // Resolve all VRegOrRef operands to concrete VRegs.
        let mut resolved_blocks: Vec<(BlockId, BlockBuilder, Vec<Operand>)> = Vec::new();
        for (id, mut b) in self.blocks {
            let operands: Vec<Operand> = b.operands.drain(..)
                .map(|val| Operand::VReg(resolve_vreg_or_ref(val, &self.refs, &mut self.regalloc)))
                .collect();
            resolved_blocks.push((id, b, operands));
        }

        let blocks = resolved_blocks.into_iter().map(|(id, b, operands)| {
            (id, IrBlock {
                id,
                vcode: b.vcode,
                operands,
                successors: successors.get(&id).cloned().unwrap_or_default(),
                predecessors: predecessors.remove(&id).unwrap_or_default(),
                params: Vec::new(),
                results: Vec::new(),
            })
        }).collect();

        IrFunction {
            regalloc: self.regalloc,
            blocks,
            block_order: order,
        }
    }

}

fn resolve_vreg_or_ref(val: VRegOrRef, refs: &[VRefSource], regalloc: &mut RegAlloc) -> VReg {
    match val {
        VRegOrRef::VReg(vreg) => vreg,
        VRegOrRef::Ref(ref_id) => {
            match refs[ref_id.0 as usize].clone() {
                VRefSource::Direct(inner) => resolve_vreg_or_ref(inner, refs, regalloc),
                VRefSource::Phi(sources) => {
                    let resolved: Vec<VReg> = sources.into_iter()
                        .map(|s| resolve_vreg_or_ref(s, refs, regalloc))
                        .collect();
                    let width = regalloc.width(resolved[0]);
                    regalloc.define(VInit::Phi(resolved), width)
                }
            }
        }
    }
}
