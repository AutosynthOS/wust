use crate::ir::VReg;
use crate::ir::VStackMut;
use crate::ir::block::BlockId;
use crate::ir::instruction::IrInst;

/// Builder for a single basic block.
///
/// Owns the mutable vstack state (depth + slot assignments) for this
/// block. When a branch targets this block, the brancher clones its
/// vstack state onto the target. When `start_block` activates this
/// block, its vstack state becomes the working state.
///
/// Tracks use/def information for VRegs:
/// - **params** = uses that weren't defined in this block (came from outside)
/// - **results** = defs still live on vstacks at block exit
pub struct BlockBuilder {
    pub(crate) id: BlockId,
    pub(crate) instructions: Vec<IrInst>,
    /// VRegs defined (created) in this block.
    pub(crate) defs: Vec<VReg>,
    /// VRegs used (consumed/read) in this block.
    pub(crate) uses: Vec<VReg>,
    /// Explicit successor blocks, set by br/br_if methods.
    pub(crate) successors: Vec<BlockId>,
    /// Whether a terminator (br, br_if, ret) has been emitted.
    pub(crate) finalized: bool,
    /// Per-vstack mutable state (depth + slots), owned by this block.
    pub(crate) vstack_state: Vec<VStackMut>,
}

impl BlockBuilder {
    pub fn new(id: BlockId) -> Self {
        Self {
            id,
            instructions: Vec::new(),
            defs: Vec::new(),
            uses: Vec::new(),
            successors: Vec::new(),
            finalized: false,
            vstack_state: Vec::new(),
        }
    }

    pub fn push(&mut self, inst: IrInst) {
        assert!(
            !self.finalized,
            "cannot emit into finalized block {:?}",
            self.id
        );
        self.instructions.push(inst);
    }

    /// Record that a VReg was defined (created) in this block.
    pub fn record_def(&mut self, vreg: VReg) {
        self.defs.push(vreg);
    }

    /// Record that a VReg was used (read/consumed) in this block.
    pub fn record_use(&mut self, vreg: VReg) {
        self.uses.push(vreg);
    }
}
