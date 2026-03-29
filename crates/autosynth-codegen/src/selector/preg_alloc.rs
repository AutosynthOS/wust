//! PReg allocation pass — resolves VReg operands to PRegs.
//!
//! Stream ordering: [inputs..., Instruction, Define(output)]
//!
//! - Operand(VReg): resolve to PReg (materialize consts first).
//! - Instruction: pass through. After it, scan forward to determine
//!   which input VRegs are dead (not used below), unbind them.
//! - Define(VReg): allocate a PReg — dead input PRegs are now free
//!   for reuse.

use std::collections::BTreeSet;

use autosynth_ir::{CodeCtx, CompileError, Operand, VCode, VReg};
use autosynth_regalloc::{RegState, VInit};
use autosynth_selector::Selector;

pub struct PRegAllocSelector<'a> {
    state: &'a mut RegState,
}

impl<'a> PRegAllocSelector<'a> {
    pub fn new(state: &'a mut RegState) -> Self {
        Self { state }
    }
}

impl Selector for PRegAllocSelector<'_> {
    fn select(&mut self, input: &mut CodeCtx) -> Result<CodeCtx, CompileError> {
        let mut output = CodeCtx::new();

        while let Some(item) = input.next() {
            match item {
                VCode::Operand(Operand::VReg(vreg)) => {
                    // Materialize consts if needed.
                    let init = self.state.alloc.borrow().init(vreg).clone();
                    if let VInit::Const(val) = init {
                        // Emit materialization: [Const(val), Materialize, Define(vreg)]
                        output.push_operand(Operand::Const(val));
                        output.push(VCode::Materialize);
                        self.state.alloc.borrow_mut().def_mut(vreg).init = VInit::InstDst;
                    }
                    let preg = self.state.alloc_preg(vreg)?;
                    output.push_operand(Operand::PReg(preg));
                }
                VCode::Operand(op) => {
                    output.push_operand(op);
                }
                VCode::Define(vreg) => {
                    // Define = VReg is born here. Allocate a PReg.
                    let preg = self.state.alloc_preg(vreg)?;
                    let init = self.state.alloc.borrow().init(vreg).clone();
                    if matches!(init, VInit::InstDst) {
                        // Instruction output — emitter needs the dst PReg.
                        output.push(VCode::DstPReg(preg));
                    }
                    // Other defs (Const, PReg, Phi) are consumed silently.
                }
                inst => {
                    // Instruction boundary — unbind dead input VRegs.
                    let live_below = scan_live_vregs(input);
                    unbind_dead_inputs(&mut output, &live_below, self.state);
                    output.push(inst);
                }
            }
        }

        Ok(output)
    }
}

/// Scan the remaining stream for all VRegs that are used.
fn scan_live_vregs(remaining: &CodeCtx) -> BTreeSet<VReg> {
    let mut live = BTreeSet::new();
    for item in &remaining.stream {
        match item {
            VCode::Operand(Operand::VReg(vreg)) => { live.insert(*vreg); }
            VCode::Define(vreg) => { live.insert(*vreg); }
            _ => {}
        }
    }
    live
}

/// Walk backwards through the output's trailing operands and unbind
/// any VRegs that aren't in the live set.
fn unbind_dead_inputs(
    output: &CodeCtx,
    live_below: &BTreeSet<VReg>,
    state: &mut RegState,
) {
    // The trailing items in output are the input operands for this
    // instruction (already resolved to PRegs). We need to find the
    // original VRegs. We can check which bound VRegs aren't live.
    for (&vreg, vstate) in state.vregs.iter() {
        if vstate.preg.is_some() && !live_below.contains(&vreg) {
            // Will be unbound below — can't mutate during iteration.
        }
    }
    // Collect then unbind.
    let to_unbind: Vec<VReg> = state.vregs.iter()
        .filter(|(_, vs)| vs.preg.is_some())
        .map(|(&v, _)| v)
        .filter(|v| !live_below.contains(v))
        .collect();
    for vreg in to_unbind {
        state.unbind(vreg);
    }
}
