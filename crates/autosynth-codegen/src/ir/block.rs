use std::collections::VecDeque;
use autosynth_ir::{BlockId, VCode, VReg};

/// A finalized block in the IR function.
pub struct IrBlock {
    pub id: BlockId,
    /// Unified VCode stream — operands and instructions interleaved.
    pub stream: VecDeque<VCode>,
    pub successors: Vec<BlockId>,
    pub predecessors: Vec<BlockId>,
    /// VRegs defined in this block.
    pub defs: Vec<VReg>,
    /// Phi VRegs this block receives from predecessors.
    pub params: Vec<VReg>,
    /// VRegs this block passes to successors.
    pub results: Vec<VReg>,
}
