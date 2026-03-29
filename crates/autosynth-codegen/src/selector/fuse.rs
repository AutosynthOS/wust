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
                // Pattern: eqz + brif
                // [val, zero, Alu(Comp(Eq)), Define(dst), Define(brif_zero), Operand(dst), Operand(brif_zero), BrIf(Ne)]
                // → [val, BrIf { Eq }]
                //
                // eqz compares val == 0, BrIf(Ne) branches when result != 0
                // (i.e. when val WAS zero). Fused: BrIf(Eq) on [val, zero]
                // branches to block_if when val == 0.
                [VCode::Operand(val), VCode::Operand(_zero),
                 VCode::Alu { op: AluOp::Comp(CompOp::Eq) }, VCode::Define(dst),
                 VCode::Define(_brif_zero),
                 VCode::Operand(Operand::VReg(use_dst)), VCode::Operand(_zero2),
                 VCode::BrIf { op: CompOp::Ne, block_if, block_else },
                 ..]
                if use_dst == dst && !is_live_after(&stream[i + 8..], *dst) => {
                    // Keep both operands — emitter needs lhs+rhs for subs.
                    // TODO: emit Cbz for single-operand form.
                    output.push_operand(*val);
                    output.push_operand(*_zero);
                    output.push(VCode::BrIf { op: CompOp::Eq, block_if: *block_if, block_else: *block_else });
                    i += 8;
                }

                // Pattern: general comp + brif
                // [lhs, rhs, Alu(Comp(op)), Define(dst), Define(brif_zero), Operand(dst), Operand(brif_zero), BrIf(Ne)]
                // → [lhs, rhs, BrIf { op }]
                [VCode::Operand(lhs), VCode::Operand(rhs),
                 VCode::Alu { op: AluOp::Comp(comp_op) }, VCode::Define(dst),
                 VCode::Define(_brif_zero),
                 VCode::Operand(Operand::VReg(use_dst)), VCode::Operand(_zero),
                 VCode::BrIf { op: CompOp::Ne, block_if, block_else },
                 ..]
                if use_dst == dst && !is_live_after(&stream[i + 8..], *dst) => {
                    output.push_operand(*lhs);
                    output.push_operand(*rhs);
                    output.push(VCode::BrIf { op: *comp_op, block_if: *block_if, block_else: *block_else });
                    i += 8;
                }

                // No match — pass through one item.
                [item, ..] => {
                    output.push(*item);
                    i += 1;
                }

                [] => break,
            }
        }

        Ok(output)
    }
}

/// Check if a VReg is used in the remaining stream (after the fused region).
fn is_live_after(remaining: &[VCode], vreg: VReg) -> bool {
    remaining.iter().any(|item| matches!(item,
        VCode::Operand(Operand::VReg(v)) if *v == vreg
    ))
}
