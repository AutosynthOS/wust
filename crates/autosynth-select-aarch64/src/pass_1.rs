use autosynth_ir::{CodeCtx, Operand, VCode};
use autosynth_isa::UImm12;
use autosynth_regalloc::{RegAlloc, VRegOr};
use autosynth_selector::SelectorError;

pub fn fold_immediates(regalloc: &mut RegAlloc, input: &mut CodeCtx) -> Result<CodeCtx, SelectorError> {
    let mut output = CodeCtx::new();
    let mut ops = input.operands.drain(..);

    for inst in input.instructions.drain(..) {
        lower_inst(regalloc, &inst, &mut ops, &mut output)?;
    }

    Ok(output)
}

fn lower_inst(
    regalloc: &mut RegAlloc,
    inst: &VCode,
    ops: &mut impl Iterator<Item = Operand>,
    output: &mut CodeCtx,
) -> Result<(), SelectorError> {
    match inst {
        VCode::Alu { .. } => {
            let lhs = ops.next().ok_or(SelectorError::OperandUnderflow)?;
            let rhs = ops.next().ok_or(SelectorError::OperandUnderflow)?;
            let dst = ops.next().ok_or(SelectorError::OperandUnderflow)?;

            let rhs = match regalloc.try_fold_imm::<UImm12>(&rhs, output) {
                VRegOr::Imm(imm) => Operand::UImm12(imm),
                VRegOr::VReg(id) => Operand::VReg(id),
            };

            output.push_operand(lhs);
            output.push_operand(rhs);
            output.push_operand(dst);
            output.push_inst(inst.clone());
        }
        _ => {
            output.push_inst(inst.clone());
        }
    }

    Ok(())
}
