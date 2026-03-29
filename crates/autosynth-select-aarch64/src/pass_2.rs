//! Pass 2: Immediate folding.
//!
//! For Alu and BrIf, try to fold the rhs operand as a UImm12
//! immediate. After pass 1's commutative swap, consts should
//! already be on the rhs where possible.

use autosynth_ir::CompileError;
use autosynth_ir::{CodeCtx, Operand, VCode};
use autosynth_isa::UImm12;
use autosynth_regalloc::SharedVRegAllocator;

pub fn fold_immediates(
    alloc: &SharedVRegAllocator,
    input: &mut CodeCtx,
) -> Result<CodeCtx, CompileError> {
    let mut output = CodeCtx::new();

    while let Some(item) = input.next() {
        match item {
            VCode::Alu { .. } => {
                let rhs = output.pop_operand_back()?;
                let lhs = output.pop_operand_back()?;

                output.push_operand(lhs);
                output.push_operand(try_fold_imm::<UImm12>(rhs, alloc));
                output.push(item);
            }
            VCode::BrIf { .. } => {
                let rhs = output.pop_operand_back()?;
                let lhs = output.pop_operand_back()?;

                output.push_operand(lhs);
                output.push_operand(try_fold_imm::<UImm12>(rhs, alloc));
                output.push(item);
            }
            other => output.push(other),
        }
    }

    Ok(output)
}

/// Try to fold a VReg operand as an immediate.
fn try_fold_imm<Imm>(op: Operand, alloc: &SharedVRegAllocator) -> Operand
where
    Imm: TryFrom<i64> + Into<Operand>,
{
    let val = match op {
        Operand::VReg(vreg) => {
            let alloc = alloc.borrow();
            match alloc.state(vreg).r#const {
                Some(val) => val,
                None => return op,
            }
        }
        Operand::Const(val) => val,
        _ => return op,
    };

    match Imm::try_from(val) {
        Ok(imm) => imm.into(),
        _ => op,
    }
}
