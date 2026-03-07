use crate::CodegenError;
use crate::backend::PhysReg;
use crate::ir::VReg;

/// A write-back register cache over canonical stack slots.
///
/// Values live canonically in memory (virtual stack slots). The regcache
/// tracks which values are currently mirrored in physical registers and
/// whether the register copy is newer than memory (dirty).
///
/// The regcache never emits instructions itself. It returns decisions
/// (e.g. "needs load", "dirty pairs to flush") that the backend lowerer
/// interprets to emit the appropriate loads, stores, and moves.
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

/// Result of [`RegCache::ensure`] — tells the lowerer which physical register
/// holds the value and whether a load from the canonical slot is needed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EnsureResult {
    /// The physical register assigned to the VReg.
    pub reg: PhysReg,
    /// If `true`, the lowerer must emit a load from the VReg's canonical slot.
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

    /// Allocate a register for a newly defined value (e.g. ALU result).
    ///
    /// If the VReg is already bound, reuses the same register. Otherwise
    /// picks the first free slot. Marks the register as dirty (the value
    /// exists only in the register, not yet stored to canonical memory).
    ///
    /// # Errors
    ///
    /// Returns [`CodegenError::RegisterExhaustion`] if no free registers
    /// remain (eviction is not yet implemented).
    pub fn define(&mut self, vreg: VReg) -> Result<PhysReg, CodegenError> {
        // Check if already bound
        if let Some(slot) = self.slots.iter_mut().find(|s| {
            s.binding.map_or(false, |b| b.vreg == vreg)
        }) {
            slot.binding = Some(Binding { vreg, dirty: true });
            return Ok(slot.reg);
        }

        // Find a free slot
        if let Some(slot) = self.slots.iter_mut().find(|s| s.binding.is_none()) {
            slot.binding = Some(Binding { vreg, dirty: true });
            return Ok(slot.reg);
        }

        // TODO: eviction
        Err(CodegenError::RegisterExhaustion)
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
        // Rebind the register to the new VReg (the old one is consumed).
        // Always dirty: the new VReg has a different canonical slot than the
        // source, so the register value hasn't been stored there yet.
        let slot = self.slots.iter_mut().find(|s| s.reg == reg).unwrap();
        slot.binding = Some(Binding { vreg: dst, dirty: true });
        Some(reg)
    }

    /// Bind a VReg to a specific physical register (clean — already in the register).
    ///
    /// Used when a value arrives in a known register (e.g., function parameters
    /// in calling convention registers). The VReg is marked clean since no
    /// store to memory is needed.
    ///
    /// # Panics
    ///
    /// Panics if `phys` is not in the scratch pool.
    pub fn bind(&mut self, vreg: VReg, phys: PhysReg) {
        self.bind_impl(vreg, phys, false);
    }

    /// Bind a VReg to a specific physical register and mark it dirty.
    ///
    /// Used when a value materializes in a register but has never been
    /// stored to its canonical memory slot (e.g., a function call return
    /// value that arrives in a calling convention register).
    ///
    /// # Panics
    ///
    /// Panics if `phys` is not in the scratch pool.
    pub fn bind_dirty(&mut self, vreg: VReg, phys: PhysReg) {
        self.bind_impl(vreg, phys, true);
    }

    fn bind_impl(&mut self, vreg: VReg, phys: PhysReg, dirty: bool) {
        let slot = self.slots.iter_mut().find(|s| s.reg == phys)
            .unwrap_or_else(|| panic!("bind: register {phys:?} not in scratch pool"));
        slot.binding = Some(Binding { vreg, dirty });
    }

    /// Ensure a VReg is in a physical register, allocating one if necessary.
    ///
    /// If the VReg is already cached, returns the register with `needs_load = false`.
    /// Otherwise picks a free register and returns `needs_load = true` so
    /// the lowerer can emit a load from the canonical stack slot.
    ///
    /// # Errors
    ///
    /// Returns [`CodegenError::RegisterExhaustion`] if no free registers
    /// remain (eviction is not yet implemented).
    pub fn ensure(&mut self, vreg: VReg) -> Result<EnsureResult, CodegenError> {
        // Already cached?
        if let Some(slot) = self.slots.iter().find(|s| {
            s.binding.map_or(false, |b| b.vreg == vreg)
        }) {
            return Ok(EnsureResult {
                reg: slot.reg,
                needs_load: false,
            });
        }

        // Need to load — find a free slot
        if let Some(slot) = self.slots.iter_mut().find(|s| s.binding.is_none()) {
            slot.binding = Some(Binding { vreg, dirty: false });
            return Ok(EnsureResult {
                reg: slot.reg,
                needs_load: true,
            });
        }

        // TODO: eviction
        Err(CodegenError::RegisterExhaustion)
    }

    /// Return all dirty (physical register, VReg) pairs whose register
    /// values are newer than memory and need to be stored back.
    ///
    /// Typically called before a function call or block exit to ensure
    /// all values are materialized to their canonical stack slots.
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

    /// Release a VReg from the cache, freeing its physical register.
    ///
    /// Used when a VReg's value was consumed without needing the register
    /// (e.g. a constant was folded into an immediate operand).
    pub fn release(&mut self, vreg: VReg) {
        if let Some(slot) = self.slots.iter_mut().find(|s| {
            s.binding.map_or(false, |b| b.vreg == vreg)
        }) {
            slot.binding = None;
        }
    }

    /// Invalidate all register bindings, marking every slot as free.
    ///
    /// Called when register contents become unreliable (e.g. after a
    /// function call that may clobber all scratch registers, or at a
    /// block boundary with unknown predecessors).
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
        let reg = cache.define(VReg(0)).unwrap();
        assert_eq!(reg, PhysReg(0));
    }

    #[test]
    fn define_then_ensure_no_load() {
        let mut cache = RegCache::new(&pool());
        let defined = cache.define(VReg(0)).unwrap();
        let result = cache.ensure(VReg(0)).unwrap();
        assert_eq!(result.reg, defined);
        assert!(!result.needs_load);
    }

    #[test]
    fn ensure_uncached_needs_load() {
        let mut cache = RegCache::new(&pool());
        let result = cache.ensure(VReg(0)).unwrap();
        assert!(result.needs_load);
    }

    #[test]
    fn define_is_dirty() {
        let mut cache = RegCache::new(&pool());
        cache.define(VReg(0)).unwrap();
        let dirty = cache.flush_dirty();
        assert_eq!(dirty, vec![(PhysReg(0), VReg(0))]);
    }

    #[test]
    fn ensure_load_is_clean() {
        let mut cache = RegCache::new(&pool());
        cache.ensure(VReg(0)).unwrap();
        let dirty = cache.flush_dirty();
        assert!(dirty.is_empty());
    }

    #[test]
    fn invalidate_clears_all() {
        let mut cache = RegCache::new(&pool());
        cache.define(VReg(0)).unwrap();
        cache.define(VReg(1)).unwrap();
        cache.invalidate_all();

        // After invalidate, ensure needs a load again
        let result = cache.ensure(VReg(0)).unwrap();
        assert!(result.needs_load);
    }

    #[test]
    fn alias_always_dirty() {
        // Regression: alias must mark the new binding dirty even if the
        // source was clean (loaded from memory). The new VReg has a
        // different canonical slot that hasn't been written yet.
        let mut cache = RegCache::new(&pool());
        let result = cache.ensure(VReg(0)).unwrap();
        assert!(result.needs_load); // v0 loaded from memory → clean
        assert!(cache.flush_dirty().is_empty()); // v0 is clean

        cache.alias(VReg(1), VReg(0)).unwrap();
        let dirty = cache.flush_dirty();
        assert_eq!(dirty.len(), 1);
        assert_eq!(dirty[0].1, VReg(1)); // v1 must be dirty
    }

    #[test]
    fn multiple_defines_use_different_regs() {
        let mut cache = RegCache::new(&pool());
        let r0 = cache.define(VReg(0)).unwrap();
        let r1 = cache.define(VReg(1)).unwrap();
        let r2 = cache.define(VReg(2)).unwrap();
        assert_ne!(r0, r1);
        assert_ne!(r1, r2);
        assert_ne!(r0, r2);
    }
}
