use std::collections::BTreeMap;
use autosynth_ir::BlockId;
use autosynth_regalloc::RegAlloc;

use super::IrBlock;

/// A completed function — finalized blocks in RPO + regalloc state.
pub struct IrFunction {
    pub regalloc: RegAlloc,
    pub blocks: BTreeMap<BlockId, IrBlock>,
    pub block_order: Vec<BlockId>,
}
