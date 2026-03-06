use super::VReg;
use super::instruction::IrInst;

/// Block identifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BlockId {
    /// Function prologue.
    Entry,
    /// Wasm-derived block, labeled by PC in the instruction stream.
    User(u32),
    /// Generated block (suspend stubs, cold paths, trampolines).
    /// Monotonic counter, no corresponding wasm PC.
    Gen(u32),
}

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
    pub id: BlockId,
    /// Values flowing into this block from predecessors.
    pub params: Vec<VReg>,
    /// Values flowing out of this block to successors.
    pub results: Vec<VReg>,
    /// Successor block IDs (from terminator analysis).
    pub successors: Vec<BlockId>,
    pub instructions: Vec<IrInst>,
}
