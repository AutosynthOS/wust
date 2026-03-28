/// AArch64 instruction selector.
///
/// Two-pass selection:
/// 1. Fold immediates (Const VRegs → UImm12 where possible)
/// 2. Resolve VRegs to PRegs based on their VInit origin
use autosynth_ir::{Operand, VCode};
use autosynth_isa::UImm12;
use autosynth_regalloc::{RegAlloc, VInit};
use autosynth_selector::{CodeCtx, Selector, SelectorError};

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
        output: &mut CodeCtx,
    ) -> Result<(), SelectorError> {
        // Pass 1: fold immediates
        let mut mid = CodeCtx::new();
        fold_immediates(regalloc, input, &mut mid)?;

        // Pass 2: resolve VRegs → PRegs
        resolve_pregs(regalloc, &mut mid, output)?;

        Ok(())
    }
}

/// Pass 1: fold Const VRegs into immediates where the instruction supports it.
fn fold_immediates(
    regalloc: &RegAlloc,
    input: &mut CodeCtx,
    output: &mut CodeCtx,
) -> Result<(), SelectorError> {
    let mut ops = input.operands.drain(..);

    for inst in input.instructions.drain(..) {
        match &inst {
            VCode::Alu { .. } => {
                let lhs = ops.next().ok_or(SelectorError::OperandUnderflow)?;
                let rhs = ops.next().ok_or(SelectorError::OperandUnderflow)?;
                let dst = ops.next().ok_or(SelectorError::OperandUnderflow)?;

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

/// Pass 2: resolve remaining VReg operands to PRegs.
///
/// - VInit::PReg(p) → Operand::PReg(p)
/// - VInit::InstDst → same PReg as the first input operand
/// - Already resolved (UImm12 etc.) → pass through
fn resolve_pregs(
    regalloc: &RegAlloc,
    input: &mut CodeCtx,
    output: &mut CodeCtx,
) -> Result<(), SelectorError> {
    let mut ops = input.operands.drain(..);

    for inst in input.instructions.drain(..) {
        match &inst {
            VCode::Alu { .. } => {
                let mut last_preg = None;
                for _ in 0..3 {
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

    Ok(())
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
