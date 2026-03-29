use std::collections::BTreeMap;

use autosynth_ir::{BlockId, CodeCtx};
use autosynth_regalloc::RegState;
use autosynth_selector::{CompileError, Selector};

use crate::selector::converge::ConvergeSelector;
use crate::selector::fuse::FuseSelector;
use crate::selector::preg_alloc::PRegAllocSelector;
use crate::ir::IrFunction;

/// A compiled function — lowered VCode blocks.
pub struct VCodeFunction {
    pub blocks: BTreeMap<BlockId, CodeCtx>,
    pub block_order: Vec<BlockId>,
}

/// Compile an IR function: converge → fuse → select → preg_alloc.
///
/// For each block:
/// 1. Convergence (emit Materialize/KeepAlive for successor params)
/// 2. Fusion (pattern-match Alu(Comp) + BrIf → fused BrIf)
/// 3. Instruction selection (immediate folding, commutative swap)
/// 4. PReg allocation (resolve VRegs to PRegs, materialize consts)
pub fn compile(
    func: &IrFunction,
    selector: &mut impl Selector,
) -> Result<VCodeFunction, CompileError> {
    let mut blocks = BTreeMap::new();
    let mut snapshots: BTreeMap<BlockId, RegState> = BTreeMap::new();

    // Entry block starts with a RegState initialized from PReg-bound defs.
    let mut entry_state = RegState::new(func.alloc.clone(), &func.config);
    {
        let alloc = func.alloc.borrow();
        for i in 0..alloc.len() {
            let vreg = autosynth_ir::VReg(i as u32);
            if let Some(preg) = alloc.state(vreg).preg {
                entry_state.bind(vreg, preg);
            }
        }
    }
    snapshots.insert(func.block_order[0], entry_state);

    for &block_id in &func.block_order {
        let block = &func.blocks[&block_id];
        let mut stream = CodeCtx { stream: block.stream.clone() };

        // 1. Convergence.
        {
            let mut converge = ConvergeSelector::new(&func.alloc, block_id, &func.blocks);
            stream = converge.select(&mut stream)?;
        }

        // 2. Fusion.
        {
            let mut fuse = FuseSelector::new();
            stream = fuse.select(&mut stream)?;
        }

        // 3. Instruction selection.
        stream = selector.select(&mut stream)?;

        // 4. PReg allocation.
        let mut state = snapshots.remove(&block_id)
            .unwrap_or_else(|| RegState::new(func.alloc.clone(), &func.config));
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
