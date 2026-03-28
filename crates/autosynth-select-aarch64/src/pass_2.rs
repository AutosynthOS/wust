use autosynth_ir::{CodeCtx, Operand, VCode};
use autosynth_isa::PReg;
use autosynth_regalloc::{RegAlloc, VInit, VRegId};
use autosynth_selector::SelectorError;

pub fn resolve_pregs(
    regalloc: &RegAlloc,
    mut input: CodeCtx,
) -> Result<CodeCtx, SelectorError> {
    let mut output = CodeCtx::new();
    let mut ops = input.operands.drain(..);

    for inst in input.instructions.drain(..) {
        match &inst {
            VCode::Alu { .. } | VCode::Materialize => {
                let mut last_preg = None;
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
    last_preg: &mut Option<PReg>,
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
