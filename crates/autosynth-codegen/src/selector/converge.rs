//! Convergence selector — inserts Materialize instructions for
//! unmaterialized const VRegs that feed into successor phi params.

use std::collections::BTreeMap;

use autosynth_ir::{BlockId, CodeCtx, CompileError, Operand, VCode, VReg};
use autosynth_regalloc::{SharedVRegAllocator, VInit};
use autosynth_selector::Selector;

use crate::ir::IrBlock;

pub struct ConvergeSelector {
    /// source VReg → (const value) for consts that need materialization.
    materializations: Vec<(VReg, i64)>,
}

impl ConvergeSelector {
    pub fn new(
        alloc: &SharedVRegAllocator,
        block_id: BlockId,
        ir_blocks: &BTreeMap<BlockId, IrBlock>,
    ) -> Self {
        let alloc = alloc.borrow();
        let current = &ir_blocks[&block_id];
        let mut materializations = Vec::new();

        for &succ_id in &current.successors {
            let succ = &ir_blocks[&succ_id];
            let pred_idx = succ.predecessors.iter()
                .position(|&p| p == block_id);
            let Some(pred_idx) = pred_idx else { continue };

            for &phi_vreg in &succ.params {
                let VInit::Phi(sources) = alloc.init(phi_vreg) else { continue };
                let Some(&source) = sources.get(pred_idx) else { continue };

                if let VInit::Const(val) = alloc.init(source) {
                    materializations.push((source, *val));
                }
            }
        }

        Self { materializations }
    }
}

impl Selector for ConvergeSelector {
    fn select(&mut self, input: &mut CodeCtx) -> Result<CodeCtx, CompileError> {
        if self.materializations.is_empty() {
            let mut output = CodeCtx::new();
            while let Some(item) = input.next() {
                output.push(item);
            }
            return Ok(output);
        }

        let mut output = CodeCtx::new();
        while let Some(item) = input.next() {
            if matches!(item, VCode::Branch { .. } | VCode::BrIf { .. }) {
                for (vreg, val) in self.materializations.drain(..) {
                    output.push_operand(Operand::Const(val));
                    output.push(VCode::Materialize);
                    output.push(VCode::Define(vreg));
                }
            }
            output.push(item);
        }

        Ok(output)
    }
}
