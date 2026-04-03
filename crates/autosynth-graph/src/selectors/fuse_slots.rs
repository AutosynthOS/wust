//! Fuse SetSlot/ClearSlot — resolve through slot bookkeeping to the
//! underlying value.

use crate::op::{Operand, VCode};
use crate::pool::Pool;
use crate::select::{SelectionCtx, Selector};

pub struct FuseSlots;

impl Selector for FuseSlots {
    fn select(&mut self, _pool: &mut Pool, ctx: &mut SelectionCtx) {
        let Some(op) = &ctx.state.op else { return; };
        if matches!(op.code, VCode::SetSlot | VCode::ClearSlot) {
            if let Operand::VReg(inner) = &op.uses[0] {
                ctx.state = inner.state().clone();
            }
        }
    }
}
