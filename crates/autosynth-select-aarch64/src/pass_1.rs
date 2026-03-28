use autosynth_ir::CompileError;
use autosynth_ir::{CodeCtx, Operand, VCode};
use autosynth_isa::UImm12;
use autosynth_regalloc::{RegAlloc, VRegOr};

pub fn fold_immediates(
    regalloc: &mut RegAlloc,
    input: &mut CodeCtx,
) -> Result<CodeCtx, CompileError> {
    let mut output = CodeCtx::new();

    while let Some(inst) = input.vcode.pop_front() {
        lower_inst(regalloc, &inst, input, &mut output)?;
    }

    Ok(output)
}

fn lower_inst(
    regalloc: &mut RegAlloc,
    inst: &VCode,
    input: &mut CodeCtx,
    output: &mut CodeCtx,
) -> Result<(), CompileError> {
    match inst {
        VCode::Alu { .. } => {
            let lhs = input.next_operand()?;
            let rhs = input.next_operand()?;
            let dst = input.next_operand()?;

            let rhs = match regalloc.imm_or_materialize::<UImm12>(rhs, output)? {
                VRegOr::Imm(imm) => Operand::UImm12(imm),
                VRegOr::VReg(vreg) => Operand::VReg(vreg),
            };

            output.operands.push_back(lhs);
            output.operands.push_back(rhs);
            output.operands.push_back(dst);
            output.vcode.push_back(inst.clone());
        }
        VCode::BrIf { .. } => {
            let lhs = input.next_operand()?;
            let rhs = input.next_operand()?;

            let rhs = match regalloc.imm_or_materialize::<UImm12>(rhs, output)? {
                VRegOr::Imm(imm) => Operand::UImm12(imm),
                VRegOr::VReg(vreg) => Operand::VReg(vreg),
            };

            output.operands.push_back(lhs);
            output.operands.push_back(rhs);
            output.vcode.push_back(inst.clone());
        }
        _ => {
            output.vcode.push_back(inst.clone());
        }
    }

    Ok(())
}
