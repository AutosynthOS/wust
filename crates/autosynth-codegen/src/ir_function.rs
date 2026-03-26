//! IR function and block types — the output of the function builder,
//! consumed by the lowerer.

use std::collections::{HashMap, HashSet};

use autosynth_ir::{BlockId, LowerInst, VReg, VRegDef, VRegRef, VRegion};
use autosynth_lower::MachineConfig;

/// A complete IR function — the finalized output of FunctionBuilder.
#[derive(Debug)]
pub struct IRFunction {
    /// Machine configuration (register pool, reservations).
    pub config: MachineConfig,
    /// Virtual region configurations, indexed by VRegionId.
    pub regions: Vec<VRegion>,
    /// All VReg definitions, indexed by Def id.
    pub vreg_defs: Vec<VRegDef>,
    /// All VReg refs, indexed by Ref id.
    pub vreg_refs: Vec<VRegRef>,
    /// Block layout order.
    pub block_order: Vec<BlockId>,
    /// All blocks, keyed by BlockId.
    pub blocks: HashMap<BlockId, IrBlock>,
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
    /// For each vreg (resolved to Def), the number of remaining uses
    /// in this block. Vregs in `results` have `usize::MAX`.
    /// Precomputed in `build()`.
    pub remaining_uses: HashMap<VReg, usize>,
}
