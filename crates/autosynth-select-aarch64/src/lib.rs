/// AArch64 instruction selector.
use autosynth_ir::{CodeCtx, Operand, VCode};
use autosynth_isa::UImm12;
use autosynth_regalloc::{RegAlloc, VInit, VRegOr};
use autosynth_selector::{Selector, SelectorError};

pub struct Aarch64Selector;

impl Aarch64Selector {
    pub fn new() -> Self {
        Self
    }
}

impl Selector for Aarch64Selector {
    fn select(
        &mut self,
        regalloc: &mut RegAlloc,
        input: &mut CodeCtx,
    ) -> Result<CodeCtx, SelectorError> {
        let mid = pass_1_fold_imms(regalloc, input)?;
        pass_2_resolve_pregs(regalloc, mid)
    }
}

fn pass_1_fold_imms(
    regalloc: &mut RegAlloc,
    input: &mut CodeCtx,
) -> Result<CodeCtx, SelectorError> {
    let mut output = CodeCtx::new();
    let mut ops = input.operands.drain(..);

    for inst in input.instructions.drain(..) {
        fold_imms_inst(regalloc, &inst, &mut ops, &mut output)?;
    }

    Ok(output)
}

fn fold_imms_inst(
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

fn pass_2_resolve_pregs(
    regalloc: &RegAlloc,
    mut input: CodeCtx,
) -> Result<CodeCtx, SelectorError> {
    let mut output = CodeCtx::new();
    let mut ops = input.operands.drain(..);

    for inst in input.instructions.drain(..) {
        match &inst {
            VCode::Alu { .. } | VCode::Materialize => {
                let mut last_preg = None;
                // Consume operands based on instruction type
                let count = match &inst {
                    VCode::Alu { .. } => 3,
                    VCode::Materialize => 2,
                    _ => 0,
                };
                for _ in 0..count {
                    let op = ops.next().ok_or(SelectorError::OperandUnderflow)?;
                    output.push_operand(resolve_operand(regalloc, op, &mut last_preg));
                }
                output.push_inst(inst);
            }
            _ => {
                output.push_inst(inst);
            }
        }
    }

    Ok(output)
}

fn resolve_operand(
    regalloc: &RegAlloc,
    op: Operand,
    last_preg: &mut Option<autosynth_isa::PReg>,
) -> Operand {
    match op {
        Operand::VReg(id) => match regalloc.init(id) {
            VInit::PReg(preg) => {
                *last_preg = Some(*preg);
                Operand::PReg(*preg)
            }
            VInit::InstDst => {
                let preg = last_preg.expect("InstDst with no prior PReg");
                Operand::PReg(preg)
            }
            _ => op,
        },
        Operand::PReg(preg) => {
            *last_preg = Some(preg);
            op
        }
        other => other,
    }
}
