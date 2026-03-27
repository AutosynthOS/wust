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

    let mut regalloc = RegAlloc::new(&func.config, &func.vreg_defs, &func.vreg_refs);
    let mut snapshots: HashMap<BlockId, MachineState> = HashMap::new();
    snapshots.insert(func.block_order[0], regalloc.state.clone());
    let mut ir_index = 0;

    for (idx, &block_id) in func.block_order.iter().enumerate() {
        let block = &func.blocks[&block_id];
        let next_block = func.block_order.get(idx + 1).copied();

        regalloc.state = snapshots[&block_id].clone();
        regalloc.begin_block(&block.remaining_uses);
        backend.bind_label(block_id);

        trace_ctx!("block", format!("{block_id:?}"));
        trace!({
            "type": "lower_block_start",
            "block": format!("{block_id:?}")
        });

        for inst in &block.instructions {
            trace_do! {
                autosynth_lower::set_group(
                    &format!("block:{block_id:?}:ir:{ir_index}")
                );
            }

            trace!({
                "type": "lower_inst",
                "ir_index": ir_index,
                "inst": autosynth_lower::__serde_json::to_value(inst).ok()
            });

            match inst {
                // Skip fall-through branches — the next block is already
                // laid out immediately after, so no jump is needed.
                LowerInst::Ir(IrInst::Branch { target }) if Some(*target) == next_block => {}
                LowerInst::Ir(ir) => {
                    trace_ctx!("origin", "lower");
                    backend.lower(&mut regalloc, ir.clone(), autosynth_lower::Emit::Fuse)?;
                    trace_do! {
                        let state_json = autosynth_lower::__serde_json::to_value(&regalloc.state).unwrap();
                        trace!({
                            "type": "regalloc_state",
                            "inst": autosynth_lower::__serde_json::to_value(ir).ok(),
                            "state": state_json
                        });
                    }
                }
                LowerInst::Reg(reg) => regalloc.process(reg, backend)?,
            }
            ir_index += 1;
        }

        // Convergence group — block-level, not tied to a specific IR instruction.
        trace_do! {
            autosynth_lower::set_group(&format!("block:{block_id:?}"));
        }

        for &succ in &block.successors {
            let into_params = &func.blocks[&succ].params;
            let into_state = snapshots
                .get(&succ)
                .cloned()
                .unwrap_or_else(|| regalloc.state.clone());
            regalloc.converge_into(block_id, into_params, &into_state, backend)?;
            if !snapshots.contains_key(&succ) {
                snapshots.insert(succ, regalloc.state.clone());
            }
        }

        backend.flush(&mut regalloc)?;
    }

    backend.finalize(&mut regalloc)?;

    trace!({
        "type": "lower_end",
        "code_size": backend.code().len()
    });

    Ok(backend.code().to_vec())
}
