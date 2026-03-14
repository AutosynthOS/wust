//! IR function and block types — the output of the function builder,
//! consumed by the lowerer.

use std::collections::{HashMap, HashSet};

use autosynth_ir::{BlockId, LowerInst, VReg, VRegDef, VRegion};

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
    /// VRegs defined in this block (via alloc_vreg).
    pub defs: HashSet<VReg>,
    /// VRegs referenced in this block (via push, pop, get_field, set_field, set_target).
    pub uses: HashSet<VReg>,
    /// VRegs that are used but not defined in this block — must come from predecessors.
    pub params: HashSet<VReg>,
    /// VRegs from this block that are needed by successor blocks' params.
    pub results: HashSet<VReg>,
    /// How many times each vreg is read by IR instructions in this block.
    /// Decremented during lowering; zero = dead, register can be freed.
    pub remaining_uses: HashMap<VReg, usize>,
}
