use crate::CodegenError;
use autosynth_isa::PReg;
use crate::ir::{VReg, VRegDef};

/// A write-back register cache over canonical stack slots.
///
/// Values live canonically in memory (virtual stack slots). The regcache
/// tracks which values are currently mirrored in physical registers and
/// whether the register copy is newer than memory (dirty).
///
/// The regcache never emits instructions itself. It returns decisions
/// (e.g. "needs load", "dirty pairs to flush", "evicted binding") that
/// the backend lowerer interprets to emit the appropriate loads, stores,
/// and moves.
pub struct RegCache {
    /// Per physical register: what VReg is cached, and is it dirty?
    slots: Vec<RegSlot>,
}

/// State of a single physical register in the cache.
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

/// Result of [`RegCache::define`] — the allocated register plus any eviction.
#[derive(Debug, Clone, Copy)]
pub struct DefineResult {
    pub reg: PReg,
    pub evicted: Option<Evicted>,
}

/// Result of [`RegCache::ensure`] — tells the lowerer which physical register
/// holds the value, whether a load is needed, and whether an eviction occurred.
#[derive(Debug, Clone, Copy)]
pub struct EnsureResult {
    /// The physical register assigned to the VReg.
    pub reg: PReg,
    /// If `true`, the lowerer must emit a load from the VReg's canonical slot
    /// (or rematerialize if the value is a constant).
    pub needs_load: bool,
    /// If an existing binding was evicted to make room.
    pub evicted: Option<Evicted>,
}

/// An evicted register binding. The backend must emit a store if
/// `needs_store` is true before reusing the register.
#[derive(Debug, Clone, Copy)]
pub struct Evicted {
    pub reg: PReg,
    pub vreg: VReg,
    /// False if the value is clean or rematerializable (no store needed).
    pub needs_store: bool,
}

impl RegCache {
    /// Create a new register cache from the available scratch pool.
    pub fn new(scratch: &[PReg]) -> Self {
        let slots = scratch
            .iter()
            .map(|&reg| RegSlot { reg, binding: None })
            .collect();
        Self { slots }
    }

    /// Allocate a register for a newly defined value (e.g. ALU result).
    ///
    /// If the VReg is already bound, reuses the same register. Otherwise
    /// picks the first free slot, or evicts if all are occupied.
    /// Marks the register as dirty.
    pub fn define(
        &mut self,
        vreg: VReg,
        vreg_defs: &[VRegDef],
    ) -> Result<DefineResult, CodegenError> {
        // Check if already bound
        if let Some(slot) = self.slots.iter_mut().find(|s| {
            s.binding.map_or(false, |b| b.vreg == vreg)
        }) {
            slot.binding = Some(Binding { vreg, dirty: true });
            return Ok(DefineResult { reg: slot.reg, evicted: None });
        }

        // Find a free slot
        if let Some(slot) = self.slots.iter_mut().find(|s| s.binding.is_none()) {
            slot.binding = Some(Binding { vreg, dirty: true });
            return Ok(DefineResult { reg: slot.reg, evicted: None });
        }

        // Evict the first slot
        let evicted = self.evict_slot(0, vreg_defs);
        self.slots[0].binding = Some(Binding { vreg, dirty: true });
        Ok(DefineResult { reg: self.slots[0].reg, evicted: Some(evicted) })
    }

    /// Check if a VReg is currently cached. Returns the register if so.
    pub fn lookup(&self, vreg: VReg) -> Option<PReg> {
        self.slots
            .iter()
            .find(|s| s.binding.map_or(false, |b| b.vreg == vreg))
            .map(|s| s.reg)
    }

    /// Alias a new VReg to the same register as an existing VReg.
    ///
    /// The new VReg shares the same physical register — no move needed.
    /// Returns the physical register, or `None` if `src` isn't cached.
    pub fn alias(&mut self, dst: VReg, src: VReg) -> Option<PReg> {
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
    pub fn bind(&mut self, vreg: VReg, phys: PReg) {
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
    pub fn bind_dirty(&mut self, vreg: VReg, phys: PReg) {
        self.bind_impl(vreg, phys, true);
    }

    fn bind_impl(&mut self, vreg: VReg, phys: PReg, dirty: bool) {
        let slot = self.slots.iter_mut().find(|s| s.reg == phys)
            .unwrap_or_else(|| panic!("bind: register {phys:?} not in scratch pool"));
        slot.binding = Some(Binding { vreg, dirty });
    }

    /// Ensure a VReg is in a physical register, allocating one if necessary.
    ///
    /// If the VReg is already cached, returns the register with `needs_load = false`.
    /// Otherwise picks a free register (or evicts) and returns `needs_load = true`
    /// so the lowerer can emit a load or rematerialize.
    pub fn ensure(
        &mut self,
        vreg: VReg,
        vreg_defs: &[VRegDef],
    ) -> Result<EnsureResult, CodegenError> {
        // Already cached?
        if let Some(slot) = self.slots.iter().find(|s| {
            s.binding.map_or(false, |b| b.vreg == vreg)
        }) {
            return Ok(EnsureResult {
                reg: slot.reg,
                needs_load: false,
                evicted: None,
            });
        }

        // Need to load — find a free slot
        if let Some(slot) = self.slots.iter_mut().find(|s| s.binding.is_none()) {
            slot.binding = Some(Binding { vreg, dirty: false });
            return Ok(EnsureResult {
                reg: slot.reg,
                needs_load: true,
                evicted: None,
            });
        }

        // Evict the first slot
        let evicted = self.evict_slot(0, vreg_defs);
        self.slots[0].binding = Some(Binding { vreg, dirty: false });
        Ok(EnsureResult {
            reg: self.slots[0].reg,
            needs_load: true,
            evicted: Some(evicted),
        })
    }

    /// Return all dirty (physical register, VReg) pairs whose register
    /// values are newer than memory and need to be stored back.
    ///
    /// Typically called before a function call or block exit to ensure
    /// all values are materialized to their canonical stack slots.
    pub fn flush_dirty(&self) -> Vec<(PReg, VReg)> {
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

    /// Evict a slot, returning the eviction info.
    ///
    /// `needs_store` is false if the value is clean or rematerializable.
    fn evict_slot(&mut self, idx: usize, vreg_defs: &[VRegDef]) -> Evicted {
        let slot = &mut self.slots[idx];
        let binding = slot.binding.take().expect("evict_slot: slot is empty");
        let remat = vreg_defs[binding.vreg.0 as usize].remat;
        Evicted {
            reg: slot.reg,
            vreg: binding.vreg,
            needs_store: binding.dirty && !remat,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use autosynth_isa::Width;
    use crate::ir::Value;

    fn pool() -> Vec<PReg> {
        vec![PReg(0), PReg(1), PReg(2)]
    }

    fn defs(n: usize) -> Vec<VRegDef> {
        (0..n)
            .map(|i| VRegDef {
                id: VReg(i as u32),
                width: Width::W32,
                slot: None,
                value: Value::ConstI64(0),
                remat: false,
            })
            .collect()
    }

    fn defs_remat(n: usize) -> Vec<VRegDef> {
        (0..n)
            .map(|i| VRegDef {
                id: VReg(i as u32),
                width: Width::W32,
                slot: None,
                value: Value::ConstI32(i as i32),
                remat: true,
            })
            .collect()
    }

    #[test]
    fn define_returns_first_free() {
        let mut cache = RegCache::new(&pool());
        let result = cache.define(VReg(0), &defs(1)).unwrap();
        assert_eq!(result.reg, PReg(0));
        assert!(result.evicted.is_none());
    }

    #[test]
    fn define_then_ensure_no_load() {
        let mut cache = RegCache::new(&pool());
        let d = defs(1);
        let defined = cache.define(VReg(0), &d).unwrap();
        let result = cache.ensure(VReg(0), &d).unwrap();
        assert_eq!(result.reg, defined.reg);
        assert!(!result.needs_load);
    }

    #[test]
    fn ensure_uncached_needs_load() {
        let mut cache = RegCache::new(&pool());
        let result = cache.ensure(VReg(0), &defs(1)).unwrap();
        assert!(result.needs_load);
    }

    #[test]
    fn define_is_dirty() {
        let mut cache = RegCache::new(&pool());
        cache.define(VReg(0), &defs(1)).unwrap();
        let dirty = cache.flush_dirty();
        assert_eq!(dirty, vec![(PReg(0), VReg(0))]);
    }

    #[test]
    fn ensure_load_is_clean() {
        let mut cache = RegCache::new(&pool());
        cache.ensure(VReg(0), &defs(1)).unwrap();
        let dirty = cache.flush_dirty();
        assert!(dirty.is_empty());
    }

    #[test]
    fn invalidate_clears_all() {
        let mut cache = RegCache::new(&pool());
        let d = defs(2);
        cache.define(VReg(0), &d).unwrap();
        cache.define(VReg(1), &d).unwrap();
        cache.invalidate_all();

        let result = cache.ensure(VReg(0), &d).unwrap();
        assert!(result.needs_load);
    }

    #[test]
    fn alias_always_dirty() {
        let mut cache = RegCache::new(&pool());
        let d = defs(2);
        let result = cache.ensure(VReg(0), &d).unwrap();
        assert!(result.needs_load);
        assert!(cache.flush_dirty().is_empty());

        cache.alias(VReg(1), VReg(0)).unwrap();
        let dirty = cache.flush_dirty();
        assert_eq!(dirty.len(), 1);
        assert_eq!(dirty[0].1, VReg(1));
    }

    #[test]
    fn multiple_defines_use_different_regs() {
        let mut cache = RegCache::new(&pool());
        let d = defs(3);
        let r0 = cache.define(VReg(0), &d).unwrap().reg;
        let r1 = cache.define(VReg(1), &d).unwrap().reg;
        let r2 = cache.define(VReg(2), &d).unwrap().reg;
        assert_ne!(r0, r1);
        assert_ne!(r1, r2);
        assert_ne!(r0, r2);
    }

    #[test]
    fn eviction_on_full_cache() {
        let mut cache = RegCache::new(&pool());
        let d = defs(4);
        cache.define(VReg(0), &d).unwrap();
        cache.define(VReg(1), &d).unwrap();
        cache.define(VReg(2), &d).unwrap();
        // Cache is full (3 slots). Next define must evict.
        let result = cache.define(VReg(3), &d).unwrap();
        assert!(result.evicted.is_some());
        let evicted = result.evicted.unwrap();
        assert_eq!(evicted.vreg, VReg(0));
        assert!(evicted.needs_store); // dirty, not remat
    }

    #[test]
    fn eviction_remat_skips_store() {
        let mut cache = RegCache::new(&pool());
        let d = defs_remat(4);
        cache.define(VReg(0), &d).unwrap();
        cache.define(VReg(1), &d).unwrap();
        cache.define(VReg(2), &d).unwrap();
        let result = cache.define(VReg(3), &d).unwrap();
        let evicted = result.evicted.unwrap();
        assert_eq!(evicted.vreg, VReg(0));
        assert!(!evicted.needs_store); // remat → no store needed
    }

    #[test]
    fn ensure_eviction_on_full_cache() {
        let mut cache = RegCache::new(&pool());
        let d = defs(4);
        cache.define(VReg(0), &d).unwrap();
        cache.define(VReg(1), &d).unwrap();
        cache.define(VReg(2), &d).unwrap();
        let result = cache.ensure(VReg(3), &d).unwrap();
        assert!(result.needs_load);
        assert!(result.evicted.is_some());
        let evicted = result.evicted.unwrap();
        assert_eq!(evicted.vreg, VReg(0));
        assert!(evicted.needs_store);
    }
}
