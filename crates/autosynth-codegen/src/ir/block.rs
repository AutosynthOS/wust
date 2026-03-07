//! Basic blocks and block identifiers.

use std::fmt;

use super::VReg;
use super::instruction::IrInst;

/// Identifies a basic block within a function.
///
/// Block IDs are used as branch targets and label keys. The three
/// variants distinguish between the function entry, caller-defined
/// blocks (typically keyed by source program counter), and
/// codegen-generated blocks (cold paths, stubs, etc.).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BlockId {
    /// Function entry / prologue block.
    Entry,
    /// Caller-defined block, keyed by a source-level index (e.g. program counter).
    User(u32),
    /// Generated block (suspend stubs, cold paths, trampolines).
    /// Uses a monotonic counter with no corresponding source-level position.
    Gen(u32),
}

impl fmt::Display for BlockId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BlockId::Entry => write!(f, "Entry"),
            BlockId::User(n) => write!(f, "L{n}"),
            BlockId::Gen(n) => write!(f, "Gen({n})"),
        }
    }
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
