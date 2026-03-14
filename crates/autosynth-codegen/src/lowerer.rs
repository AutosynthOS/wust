//! Lowerer — drives the compile loop, delegating register allocation
//! to [`RegAlloc`] which implements [`LowerCtx`] directly.

use std::collections::HashMap;

use autosynth_ir::{BlockId, LowerInst};

use crate::ir_function::IRFunction;
use crate::regalloc::{RegAlloc, RegAllocSnapshot};
use autosynth_lower::{BackendEmitter, LowerError, MachineConfig};

pub fn compile(
    config: &MachineConfig,
    func: &IRFunction,
    backend: &mut impl BackendEmitter,
) -> Result<Vec<u8>, LowerError> {
    let mut regalloc = RegAlloc::new(config, &func.vreg_defs);
    let mut snapshots: HashMap<BlockId, RegAllocSnapshot> = HashMap::new();
    let mut ir_index = 0;

    for &block_id in &func.block_order {
        let block = &func.blocks[&block_id];

        if let Some(snapshot) = snapshots.get(&block_id) {
            regalloc.restore(snapshot);
        }

        regalloc.begin_block(&block.remaining_uses, &block.results);

        for inst in &block.instructions {
            autosynth_lower::dbg(|dbg| dbg.begin_ir_inst(ir_index));
            match inst {
                LowerInst::Ir(ir) => {
                    backend.lower(&mut regalloc, ir.clone(), autosynth_lower::Emit::Fuse)?
                }
                LowerInst::Reg(reg) => regalloc.process(reg, backend)?,
            }
            ir_index += 1;
        }

        backend.flush(&mut regalloc)?;

        let snapshot = regalloc.snapshot();
        for &succ in &block.successors {
            snapshots.entry(succ).or_insert_with(|| snapshot.clone());
        }
    }

    backend.finalize(&mut regalloc)?;

    Ok(vec![])
}
