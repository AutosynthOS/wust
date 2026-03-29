//! Pass 2: Immediate folding.
//!
//! For Alu and BrIf, try to fold the rhs operand as a UImm12
//! immediate. After pass 1's commutative swap, consts should
//! already be on the rhs where possible.

use autosynth_ir::CompileError;
use autosynth_ir::{CodeCtx, Operand, VCode};
use autosynth_isa::UImm12;
use autosynth_regalloc::{SharedVRegAllocator, VInit};

pub fn fold_immediates(
    alloc: &SharedVRegAllocator,
    input: &mut CodeCtx,
) -> Result<CodeCtx, CompileError> {
    let mut output = CodeCtx::new();

    while let Some(item) = input.next() {
        match item {
            VCode::Alu { .. } => {
                let lhs = input.next_operand()?;
                let rhs = input.next_operand()?;
                let dst = input.next_operand()?;

                let rhs = try_fold_imm::<UImm12>(rhs, alloc);

                output.push(item);
                output.push_operand(lhs);
                output.push_operand(rhs);
                output.push_operand(dst);
            }
            VCode::BrIf { .. } => {
                let lhs = input.next_operand()?;
                let rhs = input.next_operand()?;

                let rhs = try_fold_imm::<UImm12>(rhs, alloc);

                output.push(item);
                output.push_operand(lhs);
                output.push_operand(rhs);
            }
            other => {
                output.push(other);
            }
        }
    }

    Ok(output)
}

/// Try to fold a VReg operand as an immediate. If the VReg is a
/// Const that fits in `Imm`, returns the folded operand.
/// Otherwise returns the original operand unchanged.
fn try_fold_imm<Imm>(op: Operand, alloc: &SharedVRegAllocator) -> Operand
where
    Imm: TryFrom<i64> + Into<Operand>,
{
    let val = match op {
        Operand::VReg(vreg) => {
            let alloc = alloc.borrow();
            match alloc.init(vreg) {
                VInit::Const(val) => *val,
                _ => return op,
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
