//! Minimal register cache for the orchestrator.
//!
//! Tracks which virtual registers are cached in physical registers
//! and whether the cached value is dirty (newer than memory).

use autosynth_ir::VReg;
use autosynth_isa::PReg;

pub struct RegCache {
    slots: Vec<RegSlot>,
}

#[derive(Debug, Clone, Copy)]
struct RegSlot {
    reg: PReg,
    binding: Option<Binding>,
}

#[derive(Debug, Clone, Copy)]
struct Binding {
    vreg: VReg,
    dirty: bool,
}

impl RegCache {
    pub fn new(pool: &[PReg]) -> Self {
        let slots = pool
            .iter()
            .map(|&reg| RegSlot { reg, binding: None })
            .collect();
        Self { slots }
    }

    /// Look up which physical register holds a vreg, if any.
    pub fn lookup(&self, vreg: VReg) -> Option<PReg> {
        self.slots
            .iter()
            .find(|s| s.binding.is_some_and(|b| b.vreg == vreg))
            .map(|s| s.reg)
    }

    /// Allocate a register for a new definition. Marks dirty.
    pub fn define(&mut self, vreg: VReg) -> PReg {
        // Already bound — reuse.
        if let Some(slot) = self
            .slots
            .iter_mut()
            .find(|s| s.binding.is_some_and(|b| b.vreg == vreg))
        {
            slot.binding = Some(Binding { vreg, dirty: true });
            return slot.reg;
        }

        // First free slot.
        if let Some(slot) = self.slots.iter_mut().find(|s| s.binding.is_none()) {
            slot.binding = Some(Binding { vreg, dirty: true });
            return slot.reg;
        }

        // TODO: eviction
        panic!("register exhaustion: no free registers and eviction not yet implemented");
    }

    /// Ensure a vreg is in a register. Returns (preg, needs_load).
    pub fn ensure(&mut self, vreg: VReg) -> (PReg, bool) {
        // Already cached.
        if let Some(slot) = self
            .slots
            .iter()
            .find(|s| s.binding.is_some_and(|b| b.vreg == vreg))
        {
            return (slot.reg, false);
        }

        // First free slot.
        if let Some(slot) = self.slots.iter_mut().find(|s| s.binding.is_none()) {
            slot.binding = Some(Binding { vreg, dirty: false });
            return (slot.reg, true);
        }

        // TODO: eviction
        panic!("register exhaustion: no free registers and eviction not yet implemented");
    }

    /// Return all dirty (preg, vreg) pairs that need storing.
    pub fn flush_dirty(&self) -> Vec<(PReg, VReg)> {
        self.slots
            .iter()
            .filter_map(|s| s.binding.filter(|b| b.dirty).map(|b| (s.reg, b.vreg)))
            .collect()
    }

    /// Mark everything as free.
    pub fn invalidate_all(&mut self) {
        for slot in &mut self.slots {
            slot.binding = None;
        }
    }

    /// Release a vreg from the cache, freeing the register.
    pub fn release(&mut self, vreg: VReg) {
        if let Some(slot) = self
            .slots
            .iter_mut()
            .find(|s| s.binding.is_some_and(|b| b.vreg == vreg))
        {
            slot.binding = None;
        }
    }
}
