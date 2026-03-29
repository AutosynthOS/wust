//! Fuser — pattern-matches VCode sequences and fuses them into
//! more efficient single instructions.
//!
//! Uses slice patterns on a contiguous view of the stream.
//! Longest patterns match first. Unmatched items pass through.
//!
//! Runs after convergence, before instruction selection.

use autosynth_ir::{AluOp, CodeCtx, CompOp, CompileError, Operand, VCode, VReg};
use autosynth_selector::Selector;

pub struct FuseSelector;

impl FuseSelector {
    pub fn new() -> Self {
        Self
    }
}

impl Selector for FuseSelector {
    fn select(&mut self, input: &mut CodeCtx) -> Result<CodeCtx, CompileError> {
        let stream = input.stream.make_contiguous();
        let mut output = CodeCtx::new();
        let mut i = 0;

        while i < stream.len() {
            match &stream[i..] {
                // Pattern: eqz + brif (or general comp + brif)
                // [val, zero, Alu(Comp(op)), DstVReg(dst), Operand(dst), Operand(zero2), BrIf(Ne)]
                // → [val, zero, BrIf { op }]
                [VCode::Operand(lhs), VCode::Operand(rhs),
                 VCode::Alu { op: AluOp::Comp(comp_op) },
                 VCode::Operand(Operand::DstVReg(dst)),
                 VCode::Operand(Operand::VReg(use_dst)), VCode::Operand(_zero),
                 VCode::BrIf { op: CompOp::Ne, block_if, block_else },
                 ..]
                if use_dst == dst && !is_live_after(&stream[i + 7..], *dst) => {
                    output.push_operand(*lhs);
                    output.push_operand(*rhs);
                    output.push(VCode::BrIf { op: *comp_op, block_if: *block_if, block_else: *block_else });
                    i += 7;
                }

                // No match — pass through one item.
                [item, ..] => {
                    output.push(item.clone());
                    i += 1;
                }

                [] => break,
            }
        }

        Ok(output)
    }
}

/// Check if a VReg is used in the remaining stream.
fn is_live_after(remaining: &[VCode], vreg: VReg) -> bool {
    remaining.iter().any(|item| matches!(item,
        VCode::Operand(Operand::VReg(v)) if *v == vreg
    ))
}
