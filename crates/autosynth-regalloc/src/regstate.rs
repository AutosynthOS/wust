//! RegState — per-block register allocation state.

use alloc::collections::BTreeMap;
use alloc::collections::btree_set::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;
use autosynth_ir::{CompileError, Operand, VReg, VRegSource, VRegState};
use autosynth_isa::PReg;

use crate::allocator::SharedVRegAllocator;
use crate::machine::MachineConfig;

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

    /// Define a new VReg with the given initial state.
    pub fn define(&mut self, state: VRegState) -> VReg {
        let bind_preg = state.preg;
        let vreg = self.alloc.borrow_mut().define(state.clone());
        self.vregs.insert(vreg, state);
        if let Some(preg) = bind_preg {
            self.bind(vreg, preg);
        }
        vreg
    }

    pub fn bind(&mut self, vreg: VReg, preg: PReg) {
        self.bindings[preg.0 as usize] = Some(vreg);
        let width = self.alloc.borrow().width(vreg);
        self.vregs
            .entry(vreg)
            .or_insert_with(|| VRegState::new(width))
            .preg = Some(preg);
    }

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

    pub fn kill_unused_bindings(&mut self, live: &BTreeSet<VReg>) {
        for preg_idx in 0..self.bindings.len() {
            let Some(vreg) = self.bindings[preg_idx] else {
                continue;
            };
            if live.contains(&vreg) {
                continue;
            }
            self.unbind(vreg);
        }
    }

    pub fn alloc_scratch(&self) -> Option<PReg> {
        self.scratch_pool
            .iter()
            .find(|p| self.bindings[p.0 as usize].is_none())
            .copied()
    }

    pub fn alloc_preg(&mut self, vreg: VReg) -> Result<PReg, CompileError> {
        if let Some(preg) = self.location(vreg) {
            return Ok(preg);
        }

        let (target, state) = {
            let alloc = self.alloc.borrow();
            let st = alloc.state(vreg);
            (st.target, st.clone())
        };

        if let Some(target) = target {
            self.bind(vreg, target);
            return Ok(target);
        }

        // Copy: reuse the source's PReg.
        if let Some(source) = state.copy {
            if let Some(preg) = self.location(source) {
                let width = self.alloc.borrow().width(vreg);
                self.vregs
                    .entry(vreg)
                    .or_insert_with(|| VRegState::new(width))
                    .preg = Some(preg);
                return Ok(preg);
            }
        }

        // Phi: find an existing PReg from sources.
        if let Some(sources) = state.phi {
            return self.alloc_phi_preg(vreg, &sources);
        }

        let preg = self.alloc_scratch().ok_or(CompileError::RegPoolExhausted)?;
        self.bind(vreg, preg);
        Ok(preg)
    }

    fn alloc_phi_preg(&mut self, phi: VReg, sources: &[VRegSource]) -> Result<PReg, CompileError> {
        let preg = sources
            .iter()
            .find_map(|s| self.location(s.vreg))
            .or_else(|| self.alloc_scratch())
            .ok_or(CompileError::RegPoolExhausted)?;

        self.bind(phi, preg);

        let mut alloc = self.alloc.borrow_mut();
        for s in sources {
            if alloc.state(s.vreg).target.is_none() {
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
