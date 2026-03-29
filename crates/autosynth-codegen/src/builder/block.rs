use autosynth_ir::{BlockId, VCode, VReg};

use super::{BuilderItem, VRegOrRef};

/// Mutable block under construction.
pub struct BlockBuilder {
    pub id: BlockId,
    /// Unified builder stream — operands (as VRegOrRef) and instructions interleaved.
    pub stream: Vec<BuilderItem>,
    /// VRegs defined while this block was current.
    pub defs: Vec<VReg>,
}

impl BlockBuilder {
    pub fn new(id: BlockId) -> Self {
        Self {
            id,
            stream: Vec::new(),
            defs: Vec::new(),
        }
    }

    pub fn emit(&mut self, inst: VCode) {
        self.stream.push(BuilderItem::Inst(inst));
    }

    pub fn push_operand(&mut self, val: impl Into<VRegOrRef>) {
        self.stream.push(BuilderItem::Operand(val.into()));
    }

    pub fn successors(&self) -> Vec<BlockId> {
        self.stream.iter().flat_map(|item| match item {
            BuilderItem::Inst(VCode::Branch { target }) => vec![*target],
            BuilderItem::Inst(VCode::BrIf { block_if, block_else, .. }) => {
                vec![*block_if, *block_else]
            }
            _ => vec![],
        }).collect()
    }
}
