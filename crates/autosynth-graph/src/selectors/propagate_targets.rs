//! Propagate target PReg constraints through view chains.
//!
//! pre_select (back to front): SetTarget records inner's hash.
//! View ops in the map propagate to their inner.
//!
//! select (front to back): check original hash against map.
//! Apply target+preg. SetTarget dissolves.

use std::collections::BTreeMap;

use autosynth_isa::PReg;

use crate::op::{Operand, VCode};
use crate::pool::Pool;
use crate::select::{SelectionCtx, Selector};

pub struct PropagateTargets {
    targets: BTreeMap<u64, PReg>,
}

impl PropagateTargets {
    pub fn new() -> Self {
        Self { targets: BTreeMap::new() }
    }
}

impl Selector for PropagateTargets {
    fn pre_select(&mut self, ctx: &SelectionCtx) {
        let Some(op) = &ctx.state.op else { return; };

        match op.code {
            VCode::SetTarget(preg) => {
                if let Operand::VReg(inner) = &op.uses[0] {
                    self.targets.insert(inner.hash_val(), preg);
                }
            }
            VCode::SetSlot | VCode::ClearSlot => {
                if let Some(&preg) = self.targets.get(&ctx.original) {
                    if let Operand::VReg(inner) = &op.uses[0] {
                        self.targets.insert(inner.hash_val(), preg);
                    }
                }
            }
            _ => {}
        }
    }

    fn select(&mut self, _pool: &mut Pool, ctx: &mut SelectionCtx) {
        let Some(op) = &ctx.state.op else { return; };

        // SetTarget → dissolve
        if let VCode::SetTarget(_) = op.code {
            if let Operand::VReg(inner) = &op.uses[0] {
                ctx.state = inner.state().clone();
                return;
            }
        }

        // Check original hash against map
        if let Some(&preg) = self.targets.get(&ctx.original) {
            ctx.state.target = Some(preg);
            ctx.state.preg = Some(preg);
        }
    }
}
