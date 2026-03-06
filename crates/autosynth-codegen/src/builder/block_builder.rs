use crate::ir::VReg;
use crate::ir::block::BlockId;
use crate::ir::instruction::IrInst;

/// Builder for a single basic block.
///
/// Collects instructions and tracks use/def information. A VReg is
/// "defined" when created within this block (push, alloc). A VReg is
/// "used" when consumed by an instruction or operation in this block
/// (pop, get_slot, push_vreg of an existing value).
///
/// At build time:
/// - **params** = uses that weren't defined in this block (came from outside)
/// - **results** = defs still live on vstacks at block exit
pub struct BlockBuilder {
    pub(crate) id: BlockId,
    pub(crate) instructions: Vec<IrInst>,
    /// VRegs defined (created) in this block.
    pub(crate) defs: Vec<VReg>,
    /// VRegs used (consumed/read) in this block.
    pub(crate) uses: Vec<VReg>,
}

impl BlockBuilder {
    pub fn new(id: BlockId) -> Self {
        Self {
            id,
            instructions: Vec::new(),
            defs: Vec::new(),
            uses: Vec::new(),
        }
    }

    pub fn push(&mut self, inst: IrInst) {
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
