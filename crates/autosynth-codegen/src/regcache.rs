//! Register cache — the state machine for vreg↔register bindings.
//!
//! Owns vreg definitions and vstack configs. Makes all decisions about
//! what to flush, when to load, and how to evict. The orchestrator
//! delegates to this; the backend queries it via LowerCtx.

use autosynth_ir::{CanonSlot, VInit, VReg, VRegDef, VRegion};
use autosynth_isa::{PReg, Width};

/// A store that the caller must emit before proceeding.
pub struct PendingStore {
    pub src: PReg,
    pub width: Width,
    pub base: PReg,
    pub offset: u32,
}

pub struct RegCache {
    /// Physical register slots — one per scratch register in the pool.
    regs: Vec<RegSlot>,
    /// Per-vreg metadata, indexed by VReg id.
    pub vreg_defs: Vec<VRegDef>,
    /// Virtual stack configs — needed to resolve canonical slot addresses.
    pub regions: Vec<VRegion>,
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
        let regs = pool
            .iter()
            .map(|&reg| RegSlot { reg, binding: None })
            .collect();
        Self {
            regs,
            vreg_defs: Vec::new(),
            regions: Vec::new(),
        }
    }

    /// Look up which physical register holds a vreg, if any.
    pub fn lookup(&self, vreg: VReg) -> Option<PReg> {
        self.regs
            .iter()
            .find(|s| s.binding.is_some_and(|b| b.vreg == vreg))
            .map(|s| s.reg)
    }

    /// Get the vreg def for a given vreg.
    pub fn def(&self, vreg: VReg) -> &VRegDef {
        &self.vreg_defs[vreg.0 as usize]
    }

    /// Resolve a canonical slot to (base PReg, byte offset).
    pub fn slot_address(&self, slot: &CanonSlot) -> (PReg, u32) {
        let region = &self.regions[slot.region.0 as usize];
        (region.base, slot.byte_offset)
    }

    /// Resolve a vreg to a physical register.
    ///
    /// Returns `(preg, width, needs_load)`. If `needs_load` is true,
    /// the caller must emit a load from the returned slot address
    /// before using the register.
    pub fn resolve(&mut self, vreg: VReg) -> ResolveResult {
        let def = self.vreg_defs[vreg.0 as usize];

        // Already cached — use directly.
        if let Some(preg) = self.lookup(vreg) {
            return ResolveResult::Ready(preg, def.width);
        }

        match def.initial {
            // VReg chain — follow to source.
            Some(VInit::CopyOf(src)) => self.resolve(src),

            // PReg — value arrived in a physical register (e.g. param).
            // Bind it in the cache (dirty — not yet stored to canonical slot).
            Some(VInit::PReg(preg)) => {
                self.bind(vreg, preg);
                ResolveResult::Ready(preg, def.width)
            }

            // Constant — defer materialization to the caller.
            Some(VInit::Const(val)) => ResolveResult::Const(val, def.width),

            // No initial — must load from canonical slot.
            None => {
                let (preg, needs_load) = self.ensure(vreg);
                if needs_load {
                    let slot = def.slot.unwrap_or_else(|| {
                        panic!("resolve: {vreg} needs load but has no canonical slot")
                    });
                    let (base, offset) = self.slot_address(&slot);
                    ResolveResult::Load(preg, def.width, base, offset)
                } else {
                    ResolveResult::Ready(preg, def.width)
                }
            }
        }
    }

    /// Allocate a physical register for a new vreg definition.
    ///
    /// If there's a target constraint, uses that register (evicting if
    /// needed). Returns `(preg, width, eviction)` — the caller must
    /// emit the eviction store if one is returned.
    pub fn define(&mut self, vreg: VReg) -> (PReg, Width, Option<PendingStore>) {
        let def = self.vreg_defs[vreg.0 as usize];
        let width = def.width;

        match def.target {
            Some(target) => {
                let eviction = self.define_at_with_eviction(vreg, target);
                (target, width, eviction)
            }
            None => {
                let preg = self.alloc(vreg);
                (preg, width, None)
            }
        }
    }

    /// Collect all stores needed before a call, then invalidate all bindings.
    ///
    /// Returns stores for dirty vregs that:
    /// - Have a canonical slot (not temps)
    /// - Are not rematerializable (not constants)
    pub fn prepare_call(&mut self) -> Vec<PendingStore> {
        let mut stores = Vec::new();
        for slot in &self.regs {
            let Some(binding) = slot.binding else {
                continue;
            };
            if !binding.dirty {
                continue;
            }

            let def = &self.vreg_defs[binding.vreg.0 as usize];

            // Constants are rematerializable — skip.
            if matches!(def.initial, Some(VInit::Const(_))) {
                continue;
            }

            // No canonical slot — temp, skip.
            let Some(canon) = &def.slot else { continue };

            let (base, offset) = self.slot_address(canon);
            stores.push(PendingStore {
                src: slot.reg,
                width: def.width,
                base,
                offset,
            });
        }

        // All scratch registers are clobbered by the call.
        for slot in &mut self.regs {
            slot.binding = None;
        }

        stores
    }

    /// Get the constant value behind a vreg, if known.
    pub fn const_value(&self, vreg: VReg) -> Option<i64> {
        let def = self.vreg_defs.get(vreg.0 as usize)?;
        match def.initial {
            Some(VInit::Const(n)) => Some(n),
            Some(VInit::CopyOf(src)) => self.const_value(src),
            _ => None,
        }
    }

    // --- Internal helpers ---

    /// Bind a vreg to a specific physical register. Marks dirty.
    fn bind(&mut self, vreg: VReg, phys: PReg) {
        let slot = match self.regs.iter_mut().find(|s| s.reg == phys) {
            Some(slot) => slot,
            None => {
                self.regs.push(RegSlot {
                    reg: phys,
                    binding: None,
                });
                self.regs.last_mut().unwrap()
            }
        };
        slot.binding = Some(Binding { vreg, dirty: true });
    }

    /// Ensure a vreg is in a register. Returns (preg, needs_load).
    fn ensure(&mut self, vreg: VReg) -> (PReg, bool) {
        // Already cached.
        if let Some(slot) = self
            .regs
            .iter()
            .find(|s| s.binding.is_some_and(|b| b.vreg == vreg))
        {
            return (slot.reg, false);
        }

        // First free slot.
        if let Some(slot) = self.regs.iter_mut().find(|s| s.binding.is_none()) {
            slot.binding = Some(Binding { vreg, dirty: false });
            return (slot.reg, true);
        }

        // TODO: eviction
        panic!("register exhaustion: no free registers and eviction not yet implemented");
    }

    /// Allocate a register for a new definition. Marks dirty.
    fn alloc(&mut self, vreg: VReg) -> PReg {
        // Already bound — reuse.
        if let Some(slot) = self
            .regs
            .iter_mut()
            .find(|s| s.binding.is_some_and(|b| b.vreg == vreg))
        {
            slot.binding = Some(Binding { vreg, dirty: true });
            return slot.reg;
        }

        // First free slot.
        if let Some(slot) = self.regs.iter_mut().find(|s| s.binding.is_none()) {
            slot.binding = Some(Binding { vreg, dirty: true });
            return slot.reg;
        }

        // TODO: eviction
        panic!("register exhaustion: no free registers and eviction not yet implemented");
    }

    /// Define a vreg into a specific physical register, returning an
    /// eviction store if something was displaced.
    fn define_at_with_eviction(&mut self, vreg: VReg, target: PReg) -> Option<PendingStore> {
        let idx = self
            .regs
            .iter()
            .position(|s| s.reg == target)
            .unwrap_or_else(|| panic!("define_at: {target:?} not in pool"));

        // Read the current binding before mutating.
        let eviction = match self.regs[idx].binding {
            Some(binding) if binding.vreg != vreg && binding.dirty => {
                let def = &self.vreg_defs[binding.vreg.0 as usize];
                if matches!(def.initial, Some(VInit::Const(_))) {
                    None
                } else if let Some(canon) = &def.slot {
                    let (base, offset) = self.slot_address(canon);
                    Some(PendingStore {
                        src: target,
                        width: def.width,
                        base,
                        offset,
                    })
                } else {
                    None
                }
            }
            _ => None,
        };

        self.regs[idx].binding = Some(Binding { vreg, dirty: true });
        eviction
    }
}

/// Result of resolving a vreg in the register cache.
pub enum ResolveResult {
    /// Value is already in this register, ready to use.
    Ready(PReg, Width),
    /// Value must be loaded from memory first.
    Load(PReg, Width, PReg, u32),
    /// Value is a known constant — materialization deferred to caller.
    Const(i64, Width),
}
