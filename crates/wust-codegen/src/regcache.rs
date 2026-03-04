/// Architecture-independent register cache.
///
/// Registers are a write-back cache over canonical wasm stack slots.
/// When a value is modified in a register, the binding is marked dirty.
/// Before suspend points or calls, dirty values must be flushed (stored)
/// to their canonical stack locations.
///
/// The cache never emits instructions — it returns decisions (need_load,
/// need_store pairs) that the caller translates into machine code.

/// Maximum number of physical registers the cache can track.
pub const MAX_REGS: usize = 16;

/// A physical register index (0-based into the scratch register pool).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RegId(pub u8);

/// A canonical wasm stack location.
///
/// Every wasm value has a known position in the stack frame — either a
/// local variable or an operand stack slot. The register cache uses this
/// as the "address" for write-back.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CanonSlot {
    /// Byte offset from x29 (frame base).
    pub byte_offset: u16,
    /// Value size in bytes (4 for i32/f32, 8 for i64/f64).
    pub size: u8,
}

/// What the cache knows about a single physical register.
#[derive(Debug, Clone, Copy)]
struct SlotBinding {
    slot: CanonSlot,
    dirty: bool,
    /// Monotonic counter — higher means more recently used.
    last_use: u32,
}

/// A register cache that tracks which canonical slots are cached in
/// which physical registers.
pub struct RegCache {
    bindings: [Option<SlotBinding>; MAX_REGS],
    /// Number of available registers in the pool.
    pool_size: u8,
    /// Monotonic use counter for LRU eviction.
    use_tick: u32,
}

/// Result of an eviction — the register freed and whether a store is needed.
pub struct EvictResult {
    pub reg: RegId,
    /// If Some, the caller must store this slot before reusing the register.
    pub spill: Option<CanonSlot>,
}

impl RegCache {
    /// Create a new register cache with `pool_size` available registers.
    pub fn new(pool_size: u8) -> Self {
        assert!(pool_size as usize <= MAX_REGS);
        RegCache {
            bindings: [None; MAX_REGS],
            pool_size,
            use_tick: 0,
        }
    }

    fn tick(&mut self) -> u32 {
        self.use_tick += 1;
        self.use_tick
    }

    /// Look up which register (if any) currently holds a canonical slot.
    pub fn find(&self, slot: CanonSlot) -> Option<RegId> {
        for i in 0..self.pool_size as usize {
            if let Some(b) = &self.bindings[i] {
                if b.slot == slot {
                    return Some(RegId(i as u8));
                }
            }
        }
        None
    }

    /// Ensure a canonical slot is in a register.
    ///
    /// Returns `(reg, needs_load)`. If `needs_load` is true, the caller
    /// must emit a load from `slot.byte_offset` into the returned register.
    pub fn ensure(&mut self, slot: CanonSlot) -> (RegId, bool) {
        // Already cached?
        if let Some(reg) = self.find(slot) {
            let t = self.tick();
            self.bindings[reg.0 as usize].as_mut().unwrap().last_use = t;
            return (reg, false);
        }
        // Allocate a register (possibly evicting).
        let EvictResult { reg, spill: _ } = self.alloc_reg();
        let t = self.tick();
        self.bindings[reg.0 as usize] = Some(SlotBinding {
            slot,
            dirty: false,
            last_use: t,
        });
        (reg, true)
    }

    /// Like `ensure` but also returns eviction spill info so the caller
    /// can emit the store before the load.
    pub fn ensure_with_evict(&mut self, slot: CanonSlot) -> (RegId, bool, Option<CanonSlot>) {
        if let Some(reg) = self.find(slot) {
            let t = self.tick();
            self.bindings[reg.0 as usize].as_mut().unwrap().last_use = t;
            return (reg, false, None);
        }
        let EvictResult { reg, spill } = self.alloc_reg();
        let t = self.tick();
        self.bindings[reg.0 as usize] = Some(SlotBinding {
            slot,
            dirty: false,
            last_use: t,
        });
        (reg, true, spill)
    }

    /// Allocate a register for a new value definition at `slot`.
    ///
    /// The value is marked dirty (register is source of truth, not memory).
    /// Returns `(reg, evict_spill)` — if evict_spill is Some, caller must
    /// store that slot before using the register.
    pub fn define(&mut self, slot: CanonSlot) -> (RegId, Option<CanonSlot>) {
        // If this slot is already cached, reuse its register.
        if let Some(reg) = self.find(slot) {
            let t = self.tick();
            let b = self.bindings[reg.0 as usize].as_mut().unwrap();
            b.dirty = true;
            b.last_use = t;
            b.slot = slot; // size might differ
            return (reg, None);
        }
        let EvictResult { reg, spill } = self.alloc_reg();
        let t = self.tick();
        self.bindings[reg.0 as usize] = Some(SlotBinding {
            slot,
            dirty: true,
            last_use: t,
        });
        (reg, spill)
    }

    /// Mark a register's binding as dirty (value has been written).
    pub fn mark_dirty(&mut self, reg: RegId) {
        if let Some(b) = self.bindings[reg.0 as usize].as_mut() {
            b.dirty = true;
        }
    }

    /// Return all dirty (reg, slot) pairs. Marks them as clean.
    ///
    /// The caller should emit stores for each returned pair.
    pub fn flush_all_dirty(&mut self) -> Vec<(RegId, CanonSlot)> {
        let mut result = Vec::new();
        for i in 0..self.pool_size as usize {
            if let Some(b) = self.bindings[i].as_mut() {
                if b.dirty {
                    result.push((RegId(i as u8), b.slot));
                    b.dirty = false;
                }
            }
        }
        result
    }

    /// Flush dirty values that are live across a call.
    ///
    /// `live_across` is the set of canonical slots that are needed after
    /// the call. Only dirty bindings matching these slots are flushed.
    pub fn flush_for_call(&mut self, live_across: &[CanonSlot]) -> Vec<(RegId, CanonSlot)> {
        let mut result = Vec::new();
        for i in 0..self.pool_size as usize {
            if let Some(b) = self.bindings[i].as_mut() {
                if b.dirty && live_across.contains(&b.slot) {
                    result.push((RegId(i as u8), b.slot));
                    b.dirty = false;
                }
            }
        }
        result
    }

    /// Invalidate all register bindings (e.g., after a call that
    /// clobbers all scratch registers).
    pub fn invalidate_all(&mut self) {
        for i in 0..self.pool_size as usize {
            self.bindings[i] = None;
        }
    }

    /// Unbind a specific register without flushing.
    pub fn unbind(&mut self, reg: RegId) {
        self.bindings[reg.0 as usize] = None;
    }

    /// Check if a register is currently bound to a slot.
    pub fn binding(&self, reg: RegId) -> Option<CanonSlot> {
        self.bindings[reg.0 as usize].map(|b| b.slot)
    }

    /// Check if a register is dirty.
    pub fn is_dirty(&self, reg: RegId) -> bool {
        self.bindings[reg.0 as usize]
            .map(|b| b.dirty)
            .unwrap_or(false)
    }

    /// Allocate a free register, evicting the LRU if none are free.
    fn alloc_reg(&mut self) -> EvictResult {
        // First, look for a free register.
        for i in 0..self.pool_size as usize {
            if self.bindings[i].is_none() {
                return EvictResult {
                    reg: RegId(i as u8),
                    spill: None,
                };
            }
        }
        // All registers occupied — evict LRU.
        self.evict_lru()
    }

    /// Evict the least-recently-used register.
    fn evict_lru(&mut self) -> EvictResult {
        let mut best_idx = 0usize;
        let mut best_tick = u32::MAX;
        for i in 0..self.pool_size as usize {
            if let Some(b) = &self.bindings[i] {
                if b.last_use < best_tick {
                    best_tick = b.last_use;
                    best_idx = i;
                }
            }
        }
        let spill = self.bindings[best_idx]
            .take()
            .filter(|b| b.dirty)
            .map(|b| b.slot);
        EvictResult {
            reg: RegId(best_idx as u8),
            spill,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn slot(offset: u16, size: u8) -> CanonSlot {
        CanonSlot {
            byte_offset: offset,
            size,
        }
    }

    #[test]
    fn ensure_loads_on_first_access() {
        let mut cache = RegCache::new(4);
        let (reg, needs_load) = cache.ensure(slot(0, 4));
        assert!(needs_load);
        assert_eq!(reg.0, 0);

        // Second access — no load needed.
        let (reg2, needs_load2) = cache.ensure(slot(0, 4));
        assert!(!needs_load2);
        assert_eq!(reg2, reg);
    }

    #[test]
    fn define_marks_dirty() {
        let mut cache = RegCache::new(4);
        let (reg, spill) = cache.define(slot(0, 4));
        assert!(spill.is_none());
        assert!(cache.is_dirty(reg));
    }

    #[test]
    fn flush_all_dirty_returns_dirty_bindings() {
        let mut cache = RegCache::new(4);
        let (r0, _) = cache.define(slot(0, 4));
        let (r1, _) = cache.ensure(slot(4, 4)); // not dirty
        let _ = r1;
        let (r2, _) = cache.define(slot(8, 4));

        let dirty = cache.flush_all_dirty();
        assert_eq!(dirty.len(), 2);
        assert!(dirty.contains(&(r0, slot(0, 4))));
        assert!(dirty.contains(&(r2, slot(8, 4))));

        // After flush, nothing is dirty.
        assert!(cache.flush_all_dirty().is_empty());
    }

    #[test]
    fn eviction_spills_dirty_lru() {
        let mut cache = RegCache::new(2);
        // Fill both registers.
        let (_r0, _) = cache.define(slot(0, 4)); // dirty, tick=1
        let (_r1, _) = cache.define(slot(4, 4)); // dirty, tick=2

        // Third define — must evict LRU (r0, tick=1).
        let (r2, spill) = cache.define(slot(8, 4));
        assert_eq!(r2.0, 0); // reused r0's physical register
        assert_eq!(spill, Some(slot(0, 4))); // r0 was dirty, must spill
    }

    #[test]
    fn eviction_skips_clean_spill() {
        let mut cache = RegCache::new(2);
        let (_r0, _) = cache.ensure(slot(0, 4)); // clean, tick=1
        let (_r1, _) = cache.define(slot(4, 4)); // dirty, tick=2

        // Evict LRU (r0) — it's clean, no spill needed.
        let (r2, spill) = cache.define(slot(8, 4));
        assert_eq!(r2.0, 0);
        assert!(spill.is_none());
    }

    #[test]
    fn invalidate_all_clears_bindings() {
        let mut cache = RegCache::new(4);
        cache.define(slot(0, 4));
        cache.define(slot(4, 4));
        cache.invalidate_all();
        assert!(cache.find(slot(0, 4)).is_none());
        assert!(cache.find(slot(4, 4)).is_none());
    }

    #[test]
    fn flush_for_call_only_flushes_live() {
        let mut cache = RegCache::new(4);
        cache.define(slot(0, 4)); // dirty
        cache.define(slot(4, 4)); // dirty
        cache.define(slot(8, 4)); // dirty

        let live = [slot(0, 4), slot(8, 4)];
        let flushed = cache.flush_for_call(&live);
        assert_eq!(flushed.len(), 2);

        // slot(4,4) is still dirty.
        assert!(cache.is_dirty(cache.find(slot(4, 4)).unwrap()));
    }

    #[test]
    fn define_same_slot_reuses_register() {
        let mut cache = RegCache::new(4);
        let (r0, _) = cache.define(slot(0, 4));
        let (r0b, spill) = cache.define(slot(0, 4));
        assert_eq!(r0, r0b);
        assert!(spill.is_none());
    }
}
