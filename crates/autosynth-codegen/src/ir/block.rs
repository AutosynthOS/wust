//! Basic blocks and block identifiers.

pub use autosynth_ir::BlockId;

use super::VReg;
use super::instruction::IrInst;

/// A basic block in the IR.
///
/// Blocks have typed params (live-in values from predecessors) and
/// results (live-out values passed to successors). At a branch to
/// block B, the brancher provides B's params. At B's terminator,
/// B provides its results to the target block's params.
///
/// This threading makes liveness explicit at every block boundary —
/// the regcache only needs to preserve what's in params/results.
#[derive(Debug)]
pub struct IrBlock {
    /// This block's identifier.
    pub id: BlockId,
    /// Values flowing into this block from predecessors (live-in VRegs).
    pub params: Vec<VReg>,
    /// Values flowing out of this block to successors (live-out VRegs).
    pub results: Vec<VReg>,
    /// Successor block IDs, extracted from the terminator instruction.
    pub successors: Vec<BlockId>,
    /// The instruction stream for this block.
    pub instructions: Vec<IrInst>,
}
