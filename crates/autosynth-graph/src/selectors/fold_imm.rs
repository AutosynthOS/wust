//! Fold const operands into UImm12 immediates where possible.

use autosynth_isa::UImm12;

use crate::op::{Operand, VCode};
use crate::pool::Pool;
use crate::select::{SelectionCtx, Selector};

pub struct FoldImm;

impl Selector for FoldImm {
    fn select(&mut self, _pool: &mut Pool, ctx: &mut SelectionCtx) {
        let Some(op) = &ctx.state.op else { return; };

        if !matches!(op.code, VCode::Alu(_)) || op.uses.len() != 2 {
            return;
        }

        let rhs_ref = match &op.uses[1] {
            Operand::VReg(r) => r,
            _ => return,
        };

        let Some(val) = rhs_ref.state().r#const else { return; };
        let Ok(imm) = UImm12::try_from(val as i32) else { return; };

        let mut op = ctx.state.op.take().unwrap();
        op.uses[1] = Operand::UImm12(imm);
        ctx.state.op = Some(op);
    }
}
