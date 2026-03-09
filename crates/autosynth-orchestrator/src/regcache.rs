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

    /// Define a vreg into a specific physical register. Marks dirty.
    ///
    /// If the target PReg is occupied by another vreg, that binding is
    /// evicted. Returns `Some((vreg, dirty))` if something was displaced.
    pub fn define_at(&mut self, vreg: VReg, target: PReg) -> Option<(VReg, bool)> {
        let slot = self.slots.iter_mut().find(|s| s.reg == target)
            .unwrap_or_else(|| panic!("define_at: {target:?} not in pool"));
        let evicted = slot.binding
            .filter(|b| b.vreg != vreg)
            .map(|b| (b.vreg, b.dirty));
        slot.binding = Some(Binding { vreg, dirty: true });
        evicted
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

    /// Bind a vreg to a specific physical register (clean).
    ///
    /// Used when a value arrives in a known register (e.g. function
    /// parameters in calling convention registers, or reserved registers
    /// like LR being pushed onto the fibre stack).
    ///
    /// If the register is not already tracked (e.g. a reserved register),
    /// a new slot is added dynamically.
    pub fn bind(&mut self, vreg: VReg, phys: PReg) {
        let slot = match self.slots.iter_mut().find(|s| s.reg == phys) {
            Some(slot) => slot,
            None => {
                self.slots.push(RegSlot {
                    reg: phys,
                    binding: None,
                });
                self.slots.last_mut().unwrap()
            }
        };
        // Dirty: the value is in the register but hasn't been stored
        // to the canonical stack slot yet (e.g. params passed in regs).
        slot.binding = Some(Binding {
            vreg,
            dirty: true,
        });
    }

    /// Alias a new vreg to the same register as an existing vreg.
    ///
    /// The new vreg shares the physical register — no move needed.
    /// Marked dirty since it has a different canonical slot.
    pub fn alias(&mut self, dst: VReg, src: VReg) {
        let reg = self
            .lookup(src)
            .unwrap_or_else(|| panic!("alias: source {src} not in cache"));
        let slot = self.slots.iter_mut().find(|s| s.reg == reg).unwrap();
        slot.binding = Some(Binding {
            vreg: dst,
            dirty: true,
        });
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
