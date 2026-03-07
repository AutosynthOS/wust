use crate::backend::PhysReg;
use crate::ir::VReg;

/// A write-back register cache over canonical stack slots.
///
/// Registers are a cache — values live canonically on the wasm stack,
/// and the regcache tracks which values are currently in physical registers
/// and whether the register value is newer than what's in memory (dirty).
///
/// The regcache never emits instructions. It returns decisions that the
/// lowerer interprets to emit loads, stores, and moves.
pub struct RegCache {
    /// Per physical register: what VReg is cached, and is it dirty?
    slots: Vec<RegSlot>,
}

/// State of a single physical register in the cache.
#[derive(Debug, Clone, Copy)]
struct RegSlot {
    reg: PhysReg,
    binding: Option<Binding>,
}

#[derive(Debug, Clone, Copy)]
struct Binding {
    vreg: VReg,
    dirty: bool,
}

/// Result of `ensure` — tells the lowerer whether a load is needed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EnsureResult {
    pub reg: PhysReg,
    pub needs_load: bool,
}

impl RegCache {
    /// Create a new register cache from the available scratch pool.
    pub fn new(scratch: &[PhysReg]) -> Self {
        let slots = scratch
            .iter()
            .map(|&reg| RegSlot { reg, binding: None })
            .collect();
        Self { slots }
    }

    /// Allocate a register for a new value (e.g. instruction result).
    /// Marks the register as dirty (value exists only in register, not yet stored).
    pub fn define(&mut self, vreg: VReg) -> PhysReg {
        // Check if already bound
        if let Some(slot) = self.slots.iter_mut().find(|s| {
            s.binding.map_or(false, |b| b.vreg == vreg)
        }) {
            slot.binding = Some(Binding { vreg, dirty: true });
            return slot.reg;
        }

        // Find a free slot
        if let Some(slot) = self.slots.iter_mut().find(|s| s.binding.is_none()) {
            slot.binding = Some(Binding { vreg, dirty: true });
            return slot.reg;
        }

        // TODO: eviction
        panic!("regcache: no free registers (eviction not yet implemented)");
    }

    /// Check if a VReg is currently cached. Returns the register if so.
    pub fn lookup(&self, vreg: VReg) -> Option<PhysReg> {
        self.slots
            .iter()
            .find(|s| s.binding.map_or(false, |b| b.vreg == vreg))
            .map(|s| s.reg)
    }

    /// Alias a new VReg to the same register as an existing VReg.
    ///
    /// The new VReg shares the same physical register — no move needed.
    /// Returns the physical register, or `None` if `src` isn't cached.
    pub fn alias(&mut self, dst: VReg, src: VReg) -> Option<PhysReg> {
        let slot = self.slots.iter().find(|s| {
            s.binding.map_or(false, |b| b.vreg == src)
        })?;
        let reg = slot.reg;
        let dirty = slot.binding.unwrap().dirty;
        // Rebind the register to the new VReg (the old one is consumed).
        let slot = self.slots.iter_mut().find(|s| s.reg == reg).unwrap();
        slot.binding = Some(Binding { vreg: dst, dirty });
        Some(reg)
    }

    /// Ensure a VReg is in a register. Returns the register and whether
    /// the lowerer needs to emit a load from the canonical stack slot.
    pub fn ensure(&mut self, vreg: VReg) -> EnsureResult {
        // Already cached?
        if let Some(slot) = self.slots.iter().find(|s| {
            s.binding.map_or(false, |b| b.vreg == vreg)
        }) {
            return EnsureResult {
                reg: slot.reg,
                needs_load: false,
            };
        }

        // Need to load — find a free slot
        if let Some(slot) = self.slots.iter_mut().find(|s| s.binding.is_none()) {
            slot.binding = Some(Binding { vreg, dirty: false });
            return EnsureResult {
                reg: slot.reg,
                needs_load: true,
            };
        }

        // TODO: eviction
        panic!("regcache: no free registers (eviction not yet implemented)");
    }

    /// Return all dirty (reg, vreg) pairs that need storing.
    pub fn flush_dirty(&self) -> Vec<(PhysReg, VReg)> {
        self.slots
            .iter()
            .filter_map(|s| {
                s.binding
                    .filter(|b| b.dirty)
                    .map(|b| (s.reg, b.vreg))
            })
            .collect()
    }

    /// Invalidate all register bindings (e.g. after a call clobbers all scratch regs).
    pub fn invalidate_all(&mut self) {
        for slot in &mut self.slots {
            slot.binding = None;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pool() -> Vec<PhysReg> {
        vec![PhysReg(0), PhysReg(1), PhysReg(2)]
    }

    #[test]
    fn define_returns_first_free() {
        let mut cache = RegCache::new(&pool());
        let reg = cache.define(VReg(0));
        assert_eq!(reg, PhysReg(0));
    }

    #[test]
    fn define_then_ensure_no_load() {
        let mut cache = RegCache::new(&pool());
        let defined = cache.define(VReg(0));
        let result = cache.ensure(VReg(0));
        assert_eq!(result.reg, defined);
        assert!(!result.needs_load);
    }

    #[test]
    fn ensure_uncached_needs_load() {
        let mut cache = RegCache::new(&pool());
        let result = cache.ensure(VReg(0));
        assert!(result.needs_load);
    }

    #[test]
    fn define_is_dirty() {
        let mut cache = RegCache::new(&pool());
        cache.define(VReg(0));
        let dirty = cache.flush_dirty();
        assert_eq!(dirty, vec![(PhysReg(0), VReg(0))]);
    }

    #[test]
    fn ensure_load_is_clean() {
        let mut cache = RegCache::new(&pool());
        cache.ensure(VReg(0));
        let dirty = cache.flush_dirty();
        assert!(dirty.is_empty());
    }

    #[test]
    fn invalidate_clears_all() {
        let mut cache = RegCache::new(&pool());
        cache.define(VReg(0));
        cache.define(VReg(1));
        cache.invalidate_all();

        // After invalidate, ensure needs a load again
        let result = cache.ensure(VReg(0));
        assert!(result.needs_load);
    }

    #[test]
    fn multiple_defines_use_different_regs() {
        let mut cache = RegCache::new(&pool());
        let r0 = cache.define(VReg(0));
        let r1 = cache.define(VReg(1));
        let r2 = cache.define(VReg(2));
        assert_ne!(r0, r1);
        assert_ne!(r1, r2);
        assert_ne!(r0, r2);
    }
}
