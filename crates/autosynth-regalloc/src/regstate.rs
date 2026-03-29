//! RegState — per-block register allocation state.

use alloc::collections::BTreeMap;
use alloc::collections::btree_set::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;
use autosynth_ir::{CompileError, Operand, VInit, VReg, VRegSource};
use autosynth_isa::{PReg, Width};

use crate::allocator::SharedVRegAllocator;
use crate::machine::MachineConfig;
use crate::state::{MemSlot, VRegState};

/// Per-block register state. Forked at branch points.
#[derive(Clone)]
pub struct RegState {
    pub alloc: SharedVRegAllocator,
    pub vregs: BTreeMap<VReg, VRegState>,
    pub bindings: Vec<Option<VReg>>,
    pub scratch_pool: Vec<PReg>,
}

impl RegState {
    pub fn new(alloc: SharedVRegAllocator, config: &MachineConfig) -> Self {
        Self {
            alloc,
            vregs: BTreeMap::new(),
            bindings: vec![None; config.num_regs],
            scratch_pool: config.scratch_pool(),
        }
    }

    /// Define a new VReg and initialize its live state.
    pub fn define(&mut self, init: VInit, width: Width) -> VReg {
        let mut state = VRegState::new(width);

        match &init {
            VInit::PReg(preg) => state.preg = Some(*preg),
            VInit::Const(val) => state.known_const = Some(*val),
            VInit::Mem(slot) => {
                state.slot = Some(MemSlot {
                    base: slot.base,
                    offset: slot.offset,
                    dirty: false,
                })
            }
            _ => {}
        }

        let bind_preg = state.preg;
        let vreg = self.alloc.borrow_mut().define(init, width);
        self.vregs.insert(vreg, state);

        if let Some(preg) = bind_preg {
            self.bind(vreg, preg);
        }

        vreg
    }

    /// Bind a VReg to a PReg.
    pub fn bind(&mut self, vreg: VReg, preg: PReg) {
        self.bindings[preg.0 as usize] = Some(vreg);
        let width = self.alloc.borrow().width(vreg);
        self.vregs
            .entry(vreg)
            .or_insert_with(|| VRegState::new(width))
            .preg = Some(preg);
    }

    /// Unbind a VReg from its PReg.
    pub fn unbind(&mut self, vreg: VReg) {
        if let Some(state) = self.vregs.get_mut(&vreg) {
            if let Some(preg) = state.preg {
                self.bindings[preg.0 as usize] = None;
            }
            state.preg = None;
        }
    }

    pub fn location(&self, vreg: VReg) -> Option<PReg> {
        self.vregs.get(&vreg).and_then(|s| s.preg)
    }

    pub fn occupant(&self, preg: PReg) -> Option<VReg> {
        self.bindings[preg.0 as usize]
    }

    /// Free PRegs whose bound VReg is not in the live set.
    pub fn kill_unused_bindings(&mut self, live: &BTreeSet<VReg>) {
        for preg_idx in 0..self.bindings.len() {
            let Some(vreg) = self.bindings[preg_idx] else { continue };
            if live.contains(&vreg) { continue; }
            self.unbind(vreg);
        }
    }

    /// Allocate a free scratch register.
    pub fn alloc_scratch(&self) -> Option<PReg> {
        self.scratch_pool
            .iter()
            .find(|p| self.bindings[p.0 as usize].is_none())
            .copied()
    }

    /// Allocate a physical register for a VReg.
    pub fn alloc_preg(&mut self, vreg: VReg) -> Result<PReg, CompileError> {
        if let Some(preg) = self.location(vreg) {
            return Ok(preg);
        }

        let (target, init) = {
            let alloc = self.alloc.borrow();
            (alloc.def(vreg).target, alloc.init(vreg).clone())
        };

        if let Some(target) = target {
            self.bind(vreg, target);
            return Ok(target);
        }

        match init {
            VInit::Copy(source) => {
                if let Some(preg) = self.location(source) {
                    let width = self.alloc.borrow().width(vreg);
                    self.vregs
                        .entry(vreg)
                        .or_insert_with(|| VRegState::new(width))
                        .preg = Some(preg);
                    return Ok(preg);
                }
            }
            VInit::Phi(sources) => {
                return self.alloc_phi_preg(vreg, &sources);
            }
            _ => {}
        }

        let preg = self.alloc_scratch().ok_or(CompileError::RegPoolExhausted)?;
        self.bind(vreg, preg);
        Ok(preg)
    }

    fn alloc_phi_preg(
        &mut self,
        phi: VReg,
        sources: &[VRegSource],
    ) -> Result<PReg, CompileError> {
        let preg = sources
            .iter()
            .find_map(|s| self.location(s.vreg))
            .or_else(|| self.alloc_scratch())
            .ok_or(CompileError::RegPoolExhausted)?;

        self.bind(phi, preg);

        let mut alloc = self.alloc.borrow_mut();
        for s in sources {
            if alloc.def(s.vreg).target.is_none() {
                alloc.set_target(s.vreg, preg);
            }
        }

        Ok(preg)
    }

    pub fn resolve_operand(&mut self, op: Operand) -> Result<Operand, CompileError> {
        match op {
            Operand::VReg(vreg) => Ok(Operand::PReg(self.alloc_preg(vreg)?)),
            other => Ok(other),
        }
    }
}
