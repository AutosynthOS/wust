//! Convergence selector — ensures phi source values are in PRegs
//! before terminal branches.
//!
//! For the first predecessor reaching a successor: materializes any
//! unmaterialized phi sources into PRegs. The resulting RegState
//! becomes the successor's contract.
//!
//! For subsequent predecessors: matches phi sources to the same PRegs
//! the contract expects.

use std::collections::BTreeMap;

use autosynth_ir::{BlockId, CodeCtx, CompileError, VCode, VReg};
use autosynth_regalloc::{RegState, SharedVRegAllocator, VInit};
use autosynth_selector::Selector;

use crate::ir::IrBlock;

/// Convergence selector — materializes/moves phi sources before
/// terminal branches so successors receive values in PRegs.
pub struct ConvergeSelector<'a> {
    alloc: SharedVRegAllocator,
    state: &'a mut RegState,
    /// Current block ID — for finding our predecessor index.
    block_id: BlockId,
    /// IrBlocks — for looking up successor params + predecessors.
    ir_blocks: &'a BTreeMap<BlockId, IrBlock>,
    /// Per-block RegState snapshots. First predecessor creates,
    /// subsequent predecessors converge into.
    snapshots: &'a mut BTreeMap<BlockId, RegState>,
}

impl<'a> ConvergeSelector<'a> {
    pub fn new(
        alloc: SharedVRegAllocator,
        state: &'a mut RegState,
        block_id: BlockId,
        ir_blocks: &'a BTreeMap<BlockId, IrBlock>,
        snapshots: &'a mut BTreeMap<BlockId, RegState>,
    ) -> Self {
        Self { alloc, state, block_id, ir_blocks, snapshots }
    }
}

impl Selector for ConvergeSelector<'_> {
    fn select(&mut self, input: &mut CodeCtx) -> Result<CodeCtx, CompileError> {
        let current = &self.ir_blocks[&self.block_id];
        if current.successors.is_empty() {
            return pass_through(input);
        }

        let actions = self.plan_convergence();
        if actions.is_empty() {
            return pass_through(input);
        }

        // Walk stream, insert materializations before the terminal.
        let mut output = CodeCtx::new();
        while let Some(item) = input.next() {
            if is_terminal(&item) {
                for action in &actions {
                    emit_action(action, self.state, &mut output)?;
                }
                output.push(item);
                while let Some(rest) = input.next() {
                    output.push(rest);
                }
                return Ok(output);
            }
            output.push(item);
        }

        Ok(output)
    }
}

/// An action to perform before a branch for phi convergence.
enum ConvergeAction {
    /// Materialize a const value into a register.
    Materialize { vreg: VReg },
}

impl ConvergeSelector<'_> {
    fn plan_convergence(&self) -> Vec<ConvergeAction> {
        let mut actions = Vec::new();
        let alloc = self.alloc.borrow();
        let current = &self.ir_blocks[&self.block_id];

        for &succ_id in &current.successors {
            let succ = &self.ir_blocks[&succ_id];

            let pred_idx = succ.predecessors.iter()
                .position(|&p| p == self.block_id);
            let Some(pred_idx) = pred_idx else { continue };

            for &phi_vreg in &succ.params {
                let VInit::Phi(sources) = alloc.init(phi_vreg) else { continue };
                let Some(&source_vreg) = sources.get(pred_idx) else { continue };

                match alloc.init(source_vreg) {
                    VInit::Const(_) => {
                        actions.push(ConvergeAction::Materialize { vreg: source_vreg });
                    }
                    _ => {
                        // TODO: emit moves if source is in wrong PReg.
                    }
                }
            }
        }

        actions
    }
}

fn emit_action(
    action: &ConvergeAction,
    state: &mut RegState,
    output: &mut CodeCtx,
) -> Result<(), CompileError> {
    match action {
        ConvergeAction::Materialize { vreg } => {
            state.materialize(*vreg, output)?;
        }
    }
    Ok(())
}

fn is_terminal(item: &VCode) -> bool {
    matches!(item, VCode::Branch { .. } | VCode::BrIf { .. } | VCode::Return)
}

fn pass_through(input: &mut CodeCtx) -> Result<CodeCtx, CompileError> {
    let mut output = CodeCtx::new();
    while let Some(item) = input.next() {
        output.push(item);
    }
    Ok(output)
}
