use std::collections::BTreeMap;

use autosynth_ir::BlockId;
use autosynth_regalloc::RegAlloc;
use autosynth_selector::{CodeCtx, Selector, SelectorError};

use crate::builder::IrFunction;

/// A compiled function — lowered VCode blocks + regalloc state.
pub struct VCodeFunction {
    pub regalloc: RegAlloc,
    pub blocks: BTreeMap<BlockId, CodeCtx>,
    pub block_order: Vec<BlockId>,
}

/// Compile an IR function through a selector.
///
/// Takes ownership of the IrFunction. Walks blocks in layout order,
/// runs the selector on each block, and collects the lowered output.
pub fn compile(
    func: IrFunction,
    selector: &mut impl Selector,
) -> Result<VCodeFunction, SelectorError> {
    let IrFunction { mut regalloc, blocks: ir_blocks, block_order } = func;
    let mut blocks = BTreeMap::new();

    for &block_id in &block_order {
        let block = &ir_blocks[&block_id];
        let mut input = CodeCtx::from(
            block.instructions.clone(),
            block.operands.clone(),
        );
        let mut output = CodeCtx::new();

        selector.select(&mut regalloc, &mut input, &mut output)?;

        blocks.insert(block_id, output);
    }

    Ok(VCodeFunction { regalloc, blocks, block_order })
}
