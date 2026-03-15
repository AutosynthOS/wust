//! Lowerer — drives the compile loop, delegating register allocation
//! to [`RegAlloc`] which implements [`LowerCtx`] directly.

use std::collections::HashMap;

use autosynth_ir::{BlockId, IrInst, LowerInst};
use autosynth_lower::{trace, trace_ctx, trace_do};

use crate::ir_function::IRFunction;
use crate::regalloc::{MachineState, RegAlloc};
use autosynth_lower::{BackendEmitter, LowerError};

pub fn compile(
    func: &IRFunction,
    backend: &mut impl BackendEmitter,
) -> Result<Vec<u8>, LowerError> {
    trace_ctx!("phase", "lower");

    let mut regalloc = RegAlloc::new(&func.config, &func.vreg_defs);
    let mut snapshots: HashMap<BlockId, MachineState> = HashMap::new();
    let mut ir_index = 0;

    for (idx, &block_id) in func.block_order.iter().enumerate() {
        let block = &func.blocks[&block_id];
        let next_block = func.block_order.get(idx + 1).copied();

        if let Some(snapshot) = snapshots.get(&block_id) {
            regalloc.state = snapshot.clone();
        }

        regalloc.state.begin_block(&block.remaining_uses, &block.results);
        backend.bind_label(block_id);

        trace_ctx!("block", format!("{block_id:?}"));
        trace!({"type": "lower_block_start", "block": format!("{block_id:?}")});

        for inst in &block.instructions {
            autosynth_lower::set_group(ir_index);

            trace_do! {
                let inst_json = autosynth_lower::__serde_json::to_value(inst).ok();
                trace!({
                    "type": "lower_inst",
                    "ir_index": ir_index,
                    "inst": inst_json
                });
            }

            match inst {
                // Skip fall-through branches — the next block is already
                // laid out immediately after, so no jump is needed.
                LowerInst::Ir(IrInst::Branch { target })
                    if Some(*target) == next_block => {}
                LowerInst::Ir(ir) => {
                    trace_ctx!("origin", "lower");
                    backend.lower(&mut regalloc, ir.clone(), autosynth_lower::Emit::Fuse)?
                }
                LowerInst::Reg(reg) => regalloc.process(reg, backend)?,
            }
            ir_index += 1;
        }

        backend.flush(&mut regalloc)?;

        let snapshot = regalloc.state.clone();
        for &succ in &block.successors {
            snapshots.entry(succ).or_insert_with(|| snapshot.clone());
        }
    }

    backend.finalize(&mut regalloc)?;

    trace!({"type": "lower_end", "code_size": backend.code().len()});

    Ok(backend.code().to_vec())
}
