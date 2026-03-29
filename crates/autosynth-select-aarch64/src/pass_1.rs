//! Pass 1: Commutative operand swap.
//!
//! For commutative ops (add, mul, and, or, xor, eq, ne), if the lhs
//! is a const and the rhs isn't, swap them so the const lands on the
//! rhs where it can be folded as an immediate in pass 2.

use autosynth_ir::{AluOp, CodeCtx, CompileError, Operand, VCode};
use autosynth_regalloc::{SharedVRegAllocator, VInit};

pub fn commutative_swap(
    alloc: &SharedVRegAllocator,
    input: &mut CodeCtx,
) -> Result<CodeCtx, CompileError> {
    let mut output = CodeCtx::new();

    while let Some(item) = input.next() {
        match item {
            VCode::Alu { op } if is_commutative(&op) => {
                let lhs = input.next_operand()?;
                let rhs = input.next_operand()?;
                let dst = input.next_operand()?;

                let (lhs, rhs) = if is_const_operand(&lhs, alloc) && !is_const_operand(&rhs, alloc) {
                    (rhs, lhs)
                } else {
                    (lhs, rhs)
                };

                output.push(item);
                output.push_operand(lhs);
                output.push_operand(rhs);
                output.push_operand(dst);
            }
            other => output.push(other),
        }
    }

    Ok(output)
}

fn is_commutative(op: &AluOp) -> bool {
    matches!(op,
        AluOp::Add | AluOp::Mul |
        AluOp::And | AluOp::Or | AluOp::Xor |
        AluOp::Comp(autosynth_ir::CompOp::Eq) |
        AluOp::Comp(autosynth_ir::CompOp::Ne)
    )
}

fn is_const_operand(op: &Operand, alloc: &SharedVRegAllocator) -> bool {
    match op {
        Operand::Const(_) => true,
        Operand::VReg(vreg) => matches!(alloc.borrow().init(*vreg), VInit::Const(_)),
        _ => false,
    }
}
