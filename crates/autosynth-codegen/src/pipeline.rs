use std::collections::BTreeMap;

use autosynth_ir::{BlockId, CodeCtx};
use autosynth_regalloc::RegState;
use autosynth_selector::{CompileError, Selector};

use crate::converge::ConvergeSelector;
use crate::ir::IrFunction;

/// A compiled function — lowered VCode blocks.
pub struct VCodeFunction {
    pub blocks: BTreeMap<BlockId, CodeCtx>,
    pub block_order: Vec<BlockId>,
}

/// Compile an IR function through a selector + convergence.
///
/// For each block:
/// 1. Run the main selector (instruction selection, immediate folding)
/// 2. Run the convergence selector (phi materialization + PReg alloc before branches)
pub fn compile(
    func: &IrFunction,
    selector: &mut impl Selector,
) -> Result<VCodeFunction, CompileError> {
    let mut blocks = BTreeMap::new();
    let mut snapshots: BTreeMap<BlockId, RegState> = BTreeMap::new();

    // Entry block starts with a fresh RegState.
    let entry_state = RegState::new(func.alloc.clone());
    snapshots.insert(func.block_order[0], entry_state);

    for &block_id in &func.block_order {
        let block = &func.blocks[&block_id];
        let mut input = CodeCtx { stream: block.stream.clone() };

        // 1. Instruction selection (pure VRegs, no PReg allocation).
        let mut selected = selector.select(&mut input)?;

        // 2. Convergence — materialize phi sources before branches.
        let mut state = snapshots.remove(&block_id)
            .unwrap_or_else(|| RegState::new(func.alloc.clone()));

        {
            let mut converge = ConvergeSelector::new(
                func.alloc.clone(),
                &mut state,
                block_id,
                &func.blocks,
                &mut snapshots,
            );
            selected = converge.select(&mut selected)?;
        }

        // Save state as snapshot for successors that don't have one yet.
        for &succ_id in &block.successors {
            if !snapshots.contains_key(&succ_id) {
                snapshots.insert(succ_id, state.clone());
            }
        }

        blocks.insert(block_id, selected);
    }

    Ok(VCodeFunction {
        blocks,
        block_order: func.block_order.clone(),
    })
}
