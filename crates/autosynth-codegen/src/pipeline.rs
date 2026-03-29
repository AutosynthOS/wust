use std::collections::BTreeMap;

use autosynth_ir::{BlockId, CodeCtx};
use autosynth_regalloc::RegState;
use autosynth_selector::{CompileError, Selector};

use crate::selector::converge::ConvergeSelector;
use crate::selector::preg_alloc::PRegAllocSelector;
use crate::ir::IrFunction;

/// A compiled function — lowered VCode blocks.
pub struct VCodeFunction {
    pub blocks: BTreeMap<BlockId, CodeCtx>,
    pub block_order: Vec<BlockId>,
}

/// Compile an IR function through select → converge → preg_alloc.
///
/// For each block:
/// 1. Instruction selection (pure VRegs, immediate folding)
/// 2. Convergence (emit Materialize for const phi sources)
/// 3. PReg allocation (resolve all VReg operands to PRegs)
pub fn compile(
    func: &IrFunction,
    selector: &mut impl Selector,
) -> Result<VCodeFunction, CompileError> {
    let mut blocks = BTreeMap::new();
    let mut snapshots: BTreeMap<BlockId, RegState> = BTreeMap::new();

    // Entry block starts with a RegState initialized from PReg-bound defs.
    let mut entry_state = RegState::new(func.alloc.clone());
    {
        let alloc = func.alloc.borrow();
        for i in 0..alloc.len() {
            let vreg = autosynth_ir::VReg(i as u32);
            if let autosynth_regalloc::VInit::PReg(preg) = alloc.init(vreg) {
                entry_state.bind(vreg, *preg);
            }
        }
    }
    snapshots.insert(func.block_order[0], entry_state);

    for &block_id in &func.block_order {
        let block = &func.blocks[&block_id];
        let mut input = CodeCtx { stream: block.stream.clone() };

        // 1. Instruction selection.
        let mut stream = selector.select(&mut input)?;

        // 2. Convergence — emit Materialize for const phi sources.
        {
            let mut converge = ConvergeSelector::new(&func.alloc, block_id, &func.blocks);
            stream = converge.select(&mut stream)?;
        }

        // 3. PReg allocation.
        let mut state = snapshots.remove(&block_id)
            .unwrap_or_else(|| RegState::new(func.alloc.clone()));
        {
            let mut preg_alloc = PRegAllocSelector::new(&mut state);
            stream = preg_alloc.select(&mut stream)?;
        }

        // Save state as snapshot for successors that don't have one yet.
        for &succ_id in &block.successors {
            if !snapshots.contains_key(&succ_id) {
                snapshots.insert(succ_id, state.clone());
            }
        }

        blocks.insert(block_id, stream);
    }

    Ok(VCodeFunction {
        blocks,
        block_order: func.block_order.clone(),
    })
}
