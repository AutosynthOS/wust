/// AArch64 instruction selector.
///
/// Transforms high-level VCode + VReg operands into lower-level VCode
/// with resolved operands (immediates, physical registers).
use autosynth_ir::{AluOp, Operand, VCode};
use autosynth_isa::UImm12;
use autosynth_regalloc::{RegAlloc, VInit};
use autosynth_selector::{CodeCtx, SelectorError};

/// AArch64 instruction selector.
pub struct Aarch64Selector;

impl Aarch64Selector {
    pub fn new() -> Self {
        Self
    }

    /// Run selection on a block.
    pub fn select(
        &mut self,
        regalloc: &mut RegAlloc,
        input: &mut CodeCtx,
        output: &mut CodeCtx,
    ) -> Result<(), SelectorError> {
        let mut ops = input.operands.drain(..).peekable();

        for inst in input.instructions.drain(..) {
            match &inst {
                VCode::Alu { op } => {
                    let lhs = ops.next().ok_or(SelectorError::OperandUnderflow)?;
                    let rhs = ops.next().ok_or(SelectorError::OperandUnderflow)?;
                    let dst = ops.next().ok_or(SelectorError::OperandUnderflow)?;

                    // Both const → fold entirely at compile time.
                    if let (Some(l), Some(r)) = (try_const(regalloc, &lhs), try_const(regalloc, &rhs)) {
                        if let Some(result) = eval_const_alu(op, l, r) {
                            let Operand::VReg { id: dst_id, .. } = dst else {
                                unreachable!("Alu dst must be VReg");
                            };
                            regalloc.set_init(dst_id, VInit::Const(result));
                            continue;
                        }
                    }

                    // Rhs const fits UImm12 → fold immediate.
                    output.push_operand(lhs);
                    output.push_operand(try_fold_uimm12(regalloc, rhs));
                    output.push_operand(dst);
                    output.push_inst(inst);
                }
                _ => {
                    output.push_inst(inst);
                }
            }
        }

        Ok(())
    }
}

/// If the operand is a VReg with Const origin, return the value.
fn try_const(regalloc: &RegAlloc, op: &Operand) -> Option<i64> {
    let Operand::VReg { id, .. } = op else { return None };
    let VInit::Const(val) = regalloc.init(*id) else { return None };
    Some(*val)
}

/// Try to fold a VReg operand as a UImm12 if it's a small constant.
fn try_fold_uimm12(regalloc: &RegAlloc, op: Operand) -> Operand {
    let Some(val) = try_const(regalloc, &op) else { return op };
    match UImm12::try_from(val) {
        Ok(imm) => Operand::UImm12(imm),
        Err(_) => op,
    }
}

/// Evaluate an ALU op on two constant values.
fn eval_const_alu(op: &AluOp, lhs: i64, rhs: i64) -> Option<i64> {
    match op {
        AluOp::Add => Some(lhs.wrapping_add(rhs)),
        AluOp::Sub => Some(lhs.wrapping_sub(rhs)),
        AluOp::Mul => Some(lhs.wrapping_mul(rhs)),
        _ => None,
    }
}
