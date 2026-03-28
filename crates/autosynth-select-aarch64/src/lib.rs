/// AArch64 instruction selector.
///
/// Transforms high-level VCode + VReg operands into lower-level VCode
/// with resolved operands (immediates, physical registers).
use autosynth_ir::{Operand, VCode};
use autosynth_isa::UImm12;
use autosynth_regalloc::RegAlloc;
use autosynth_selector::{CodeCtx, SelectorError};

pub struct Aarch64Selector;

impl Aarch64Selector {
    pub fn new() -> Self {
        Self
    }

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

                    // Rhs const fits UImm12 → fold immediate.
                    let rhs = match regalloc.try_fold_imm::<UImm12>(&rhs) {
                        Some(imm) => Operand::UImm12(imm),
                        None => rhs,
                    };

                    output.push_operand(lhs);
                    output.push_operand(rhs);
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
