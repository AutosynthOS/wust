//! Convergence selector — ensures all successor block params
//! survive to the branch point.
//!
//! For const values: emits Materialize + Define before the branch.
//! For already-live values: emits KeepAlive to prevent unbinding.

use std::collections::BTreeMap;

use autosynth_ir::{BlockId, CodeCtx, CompileError, Operand, VCode, VReg};
use autosynth_regalloc::SharedVRegAllocator;
use autosynth_selector::Selector;

use crate::ir::IrBlock;

enum ConvergeOp {
    Materialize { vreg: VReg, val: i64 },
    KeepAlive(VReg),
}

pub struct ConvergeSelector {
    ops: Vec<ConvergeOp>,
}

impl ConvergeSelector {
    pub fn new(
        alloc: &SharedVRegAllocator,
        block_id: BlockId,
        ir_blocks: &BTreeMap<BlockId, IrBlock>,
    ) -> Self {
        let alloc = alloc.borrow();
        let current = &ir_blocks[&block_id];
        let mut ops = Vec::new();

        for &succ_id in &current.successors {
            let succ = &ir_blocks[&succ_id];

            for &param in &succ.params {
                let param_state = alloc.state(param);
                match &param_state.phi {
                    Some(sources) => {
                        let Some(source) = sources.iter().find(|s| s.block == block_id) else { continue };
                        let source_state = alloc.state(source.vreg);
                        match source_state.r#const {
                            Some(val) => {
                                ops.push(ConvergeOp::Materialize { vreg: source.vreg, val });
                            }
                            None => todo!("handle cases where phi source is not a const"),
                        }
                    }
                    None => {
                        ops.push(ConvergeOp::KeepAlive(param));
                    }
                }
            }
        }

        Self { ops }
    }
}

impl Selector for ConvergeSelector {
    fn select(&mut self, input: &mut CodeCtx) -> Result<CodeCtx, CompileError> {
        if self.ops.is_empty() {
            let mut output = CodeCtx::new();
            while let Some(item) = input.next() {
                output.push(item);
            }
            return Ok(output);
        }

        let mut output = CodeCtx::new();
        while let Some(item) = input.next() {
            if matches!(item, VCode::Branch { .. } | VCode::BrIf { .. }) {
                for op in self.ops.drain(..) {
                    match op {
                        ConvergeOp::Materialize { vreg, val } => {
                            output.push_operand(Operand::Const(val));
                            output.push(VCode::Materialize);
                            output.push_operand(Operand::DstVReg(vreg));
                        }
                        ConvergeOp::KeepAlive(vreg) => {
                            output.push(VCode::KeepAlive);
                            output.push_operand(Operand::VReg(vreg));
                        }
                    }
                }
            }
            output.push(item);
        }

        Ok(output)
    }
}
