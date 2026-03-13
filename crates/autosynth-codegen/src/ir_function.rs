//! IR function and block types — the output of the function builder,
//! consumed by the lowerer.

use autosynth_ir::{BlockId, LowerInst, VRegDef, VRegion};

/// A complete IR function — the finalized output of FunctionBuilder.
#[derive(Debug)]
pub struct IRFunction {
    /// Virtual region configurations, indexed by VRegionId.
    pub regions: Vec<VRegion>,
    /// All VReg definitions, indexed by VReg id.
    pub vreg_defs: Vec<VRegDef>,
    /// Block layout order.
    pub block_order: Vec<BlockId>,
    /// All blocks, keyed by BlockId.
    pub blocks: std::collections::HashMap<BlockId, IrBlock>,
}

/// A basic block in the IR.
#[derive(Debug)]
pub struct IrBlock {
    /// Successor block IDs.
    pub successors: Vec<BlockId>,
    /// The instruction stream for this block — IR and register ops interleaved.
    pub instructions: Vec<LowerInst>,
    /// Whether a terminator (br, br_if, ret) has been emitted.
    pub finalized: bool,
}
