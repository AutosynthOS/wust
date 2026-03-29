//! PReg allocation pass — resolves VReg operands to PRegs.
//!
//! Stream ordering: [inputs..., Instruction, Define(output)]
//!
//! - Operand(VReg): resolve to PReg (materialize consts first).
//! - Instruction: pass through. After it, scan forward to determine
//!   which input VRegs are dead (not used below), unbind them.
//! - Define(VReg): allocate a PReg — dead input PRegs are now free
//!   for reuse.

use autosynth_ir::{CodeCtx, CompileError, Operand, VCode, VReg};
use autosynth_regalloc::RegState;
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
                    let alloc = self.state.alloc.borrow();
                    let konst = alloc.state(vreg).r#const;
                    drop(alloc);
                    if let Some(val) = konst {
                        output.push_operand(Operand::Const(val));
                        output.push(VCode::Materialize);
                        self.state.alloc.borrow_mut().state_mut(vreg).inst_dst = true;
                    }
                    let preg = self.state.alloc_preg(vreg)?;
                    output.push_operand(Operand::PReg(preg));
                }
                VCode::Operand(Operand::DstVReg(vreg)) => {
                    let preg = self.state.alloc_preg(vreg)?;
                    let width = self.state.alloc.borrow().width(vreg);
                    output.push_operand(Operand::DstPReg(preg, width));
                }
                VCode::Operand(op) => {
                    output.push_operand(op);
                }
                VCode::Define(vreg) => {
                    let state = self.state.alloc.borrow().state(vreg).clone();
                    let bind_preg = state.preg;
                    self.state.vregs.insert(vreg, state);
                    if let Some(preg) = bind_preg {
                        self.state.bind(vreg, preg);
                    }
                }
                VCode::KeepAlive => {
                    let _ = input.next_operand();
                }
                VCode::SetSlot { vreg, slot } => {
                    if let Some(vs) = self.state.vregs.get_mut(&vreg) {
                        vs.slot = Some(autosynth_regalloc::MemSlot {
                            base: slot.base,
                            offset: slot.offset,
                            dirty: false,
                        });
                    }
                }
                VCode::ClearSlot(vreg) => {
                    if let Some(vs) = self.state.vregs.get_mut(&vreg) {
                        vs.slot = None;
                    }
                }
                // Instruction boundary
                inst => {
                    // Kill any vregs that should are no longer
                    // needed after this instruction...
                    self.state.kill_unused_bindings(&input.live_vregs());

                    // finally, emit the instruction
                    output.push(inst);
                }
            }
        }

        Ok(output)
    }
}
