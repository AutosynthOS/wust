//! SpillReload — track used vregs, emit Needs at calls, reset.

use std::collections::{BTreeMap, BTreeSet};
use std::task::ready;

use crate::Op;
use crate::node::NodeRef;
use crate::op::{Operand, VCode};
use crate::pool::Pool;
use crate::select::{SelectionCtx, Selector};
use crate::state::VRegState;

pub struct SpillReload {
    used: BTreeSet<NodeRef>,
    call_uses: BTreeMap<u64, BTreeSet<NodeRef>>,
}

impl SpillReload {
    pub fn new() -> Self {
        Self {
            used: BTreeSet::new(),
            call_uses: BTreeMap::new(),
        }
    }
}

impl Selector for SpillReload {
    fn reset(&mut self) {
        let _ = std::mem::take(&mut self.used);
        let _ = std::mem::take(&mut self.call_uses);
    }
    fn pre_select(&mut self, ctx: &SelectionCtx) {
        let Some(op) = &ctx.state.op else {
            return;
        };

        match op.code {
            // Save the uses of a call for later emission
            VCode::Call(..) => {
                let used = std::mem::take(&mut self.used);
                self.call_uses.insert(ctx.original, used);
            }
            // we don't want to track uses for Needs
            // because they're already always loaded
            VCode::Needs => {}
            _ => {
                // Track every VReg operand as used
                for operand in &op.uses {
                    if let Operand::VReg(r) = operand {
                        self.used.insert(r.clone());
                    }
                }
            }
        }
    }

    fn select(&mut self, pool: &mut Pool, ctx: &mut SelectionCtx) {
        if !matches!(
            ctx.state.op,
            Some(Op {
                code: VCode::Call(_),
                ..
            })
        ) {
            return;
        }

        let uses = self
            .call_uses
            .remove(&ctx.original)
            .unwrap_or_default()
            .into_iter()
            .map(Operand::VReg)
            .collect();

        let call_ref = pool.intern(ctx.state.clone());

        let needs = pool.intern(VRegState {
            op: Some(crate::op::Op {
                code: VCode::Needs,
                uses,
                // effect: Some(call_ref),
                effect: None,
            }),
            ..VRegState::new(autosynth_isa::Width::W32)
        });

        ctx.state = needs.state().clone();

        // ctx.state.op.as_mut().map(|op| op.effect = Some(needs));
    }
}
