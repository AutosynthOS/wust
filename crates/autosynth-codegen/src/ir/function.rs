use std::collections::BTreeMap;
use autosynth_ir::BlockId;
use autosynth_regalloc::SharedVRegAllocator;

use super::IrBlock;

/// A completed function — finalized blocks in RPO + shared VReg allocator.
pub struct IrFunction {
    pub alloc: SharedVRegAllocator,
    pub blocks: BTreeMap<BlockId, IrBlock>,
    pub block_order: Vec<BlockId>,
}
