//! Register allocator — running state machine that tracks vreg
//! locations and manages physical register bindings.
//!
//! Uses a reference count (`remaining_uses`) per vreg to know when
//! a vreg is dead and its register can be freed. No instruction
//! index tracking needed.

use std::collections::HashMap;

use autosynth_ir::{IrInst, RegInst, SlotRef, VInit, VReg, VRegDef};
use autosynth_isa::{PReg, Width};
use autosynth_lower::{BackendEmitter, LowerCtx, LowerError, ResolvedVReg};

#[derive(Debug, Clone)]
enum VRegLoc {
    Const(i64),
    Pending,
    Reg(PReg),
    Mem,
}

#[derive(Debug, Clone)]
struct SlotState {
    slot: SlotRef,
    dirty: bool,
}

#[derive(Debug, Clone)]
struct VRegEntry {
    loc: VRegLoc,
    slots: Vec<SlotState>,
}

pub(crate) struct RegAlloc {
    vreg_defs: Vec<VRegDef>,
    entries: Vec<Option<VRegEntry>>,
    bindings: Vec<Option<VReg>>,
    allocatable: Vec<PReg>,
    /// Per-vreg remaining use count. Decremented on resolve.
    /// Zero = dead, register can be freed.
    remaining: HashMap<VReg, usize>,
    /// VRegs that must stay alive until block exit.
    results: Vec<VReg>,
}

impl RegAlloc {
    pub(crate) fn new(scratch_pool: &[PReg]) -> Self {
        let max_reg = scratch_pool
            .iter()
            .map(|p| p.0 as usize)
            .max()
            .unwrap_or(31);
        Self {
            vreg_defs: Vec::new(),
            entries: Vec::new(),
            bindings: vec![None; max_reg + 1],
            allocatable: scratch_pool.to_vec(),
            remaining: HashMap::new(),
            results: Vec::new(),
        }
    }

    pub(crate) fn reset(&mut self, vreg_defs: Vec<VRegDef>) {
        let count = vreg_defs.len();
        self.vreg_defs = vreg_defs;
        self.entries.clear();
        self.entries.resize(count, None);
    }

    pub(crate) fn begin_block(
        &mut self,
        remaining_uses: &HashMap<VReg, usize>,
        results: &std::collections::HashSet<VReg>,
    ) {
        self.remaining = remaining_uses.clone();
        self.results = results.iter().copied().collect();
    }

    pub(crate) fn vreg_width(&self, vreg: VReg) -> Width {
        self.vreg_defs[vreg.0 as usize].width
    }

    fn entry(&self, vreg: VReg) -> Result<&VRegEntry, LowerError> {
        self.entries[vreg.0 as usize]
            .as_ref()
            .ok_or(LowerError::UndefinedVReg(vreg))
    }

    fn entry_mut(&mut self, vreg: VReg) -> Result<&mut VRegEntry, LowerError> {
        self.entries[vreg.0 as usize]
            .as_mut()
            .ok_or(LowerError::UndefinedVReg(vreg))
    }

    fn is_live(&self, vreg: VReg) -> bool {
        if self.results.contains(&vreg) {
            return true;
        }
        self.remaining.get(&vreg).map(|&n| n > 0).unwrap_or(false)
    }

    /// Decrement remaining uses. If it hits zero and the vreg isn't
    /// in results, free its register.
    fn consume(&mut self, vreg: VReg) {
        if let Some(count) = self.remaining.get_mut(&vreg) {
            *count = count.saturating_sub(1);
            if *count == 0 && !self.results.contains(&vreg) {
                if let Some(entry) = &self.entries[vreg.0 as usize] {
                    if let VRegLoc::Reg(preg) = entry.loc {
                        self.bindings[preg.0 as usize] = None;
                    }
                }
            }
        }
    }

    // --- RegInst processing ---

    pub(crate) fn process(
        &mut self,
        inst: &RegInst,
        backend: &mut impl BackendEmitter,
    ) -> Result<(), LowerError> {
        match inst {
            RegInst::Define { vreg, value } => {
                let idx = vreg.0 as usize;
                if self.entries[idx].is_some() {
                    return Err(LowerError::DuplicateDefine(*vreg));
                }
                let loc = match value {
                    VInit::Const(val) => VRegLoc::Const(*val),
                    VInit::PReg(preg) => {
                        self.acquire(*preg, backend)?;
                        self.bindings[preg.0 as usize] = Some(*vreg);
                        VRegLoc::Reg(*preg)
                    }
                    VInit::InstDst => VRegLoc::Pending,
                };
                self.entries[idx] = Some(VRegEntry {
                    loc,
                    slots: Vec::new(),
                });
                Ok(())
            }
            RegInst::SetSlot { vreg, slot } => {
                self.entry_mut(*vreg)?.slots.push(SlotState {
                    slot: *slot,
                    dirty: true,
                });
                Ok(())
            }
            RegInst::ClearSlot { vreg, slot } => {
                self.entry_mut(*vreg)?.slots.retain(|s| s.slot != *slot);
                Ok(())
            }
        }
    }

    // --- Eviction ---

    fn acquire(&mut self, preg: PReg, backend: &mut impl BackendEmitter) -> Result<PReg, LowerError> {
        let victim = match self.bindings[preg.0 as usize] {
            Some(v) => v,
            None => return Ok(preg),
        };

        if !self.is_live(victim) || matches!(self.entry(victim)?.loc, VRegLoc::Const(_)) {
            self.bindings[preg.0 as usize] = None;
            return Ok(preg);
        }

        // Live vreg — try move, fall back to spill.
        let width = self.vreg_width(victim);
        match self.alloc_reg() {
            Ok(dest) => {
                backend.lower(self, IrInst::Move {
                    dst: dest,
                    dst_width: width,
                    src: preg,
                    src_width: width,
                })?;
                self.bindings[dest.0 as usize] = Some(victim);
                self.bindings[preg.0 as usize] = None;
                self.entry_mut(victim)?.loc = VRegLoc::Reg(dest);
            }
            Err(_) => {
                self.flush_vreg(victim, preg, width, backend)?;
            }
        }
        Ok(preg)
    }

    fn flush_vreg(
        &mut self,
        vreg: VReg,
        preg: PReg,
        width: Width,
        backend: &mut impl BackendEmitter,
    ) -> Result<(), LowerError> {
        let slot = self.entry(vreg)?
            .slots
            .iter()
            .find(|s| s.dirty)
            .map(|s| s.slot)
            .ok_or(LowerError::UndefinedVReg(vreg))?;
        backend.lower(self, IrInst::Store {
            src: preg,
            width,
            base: slot.base,
            offset: slot.offset,
        })?;
        let entry = self.entry_mut(vreg)?;
        for s in &mut entry.slots {
            s.dirty = false;
        }
        entry.loc = VRegLoc::Mem;
        self.bindings[preg.0 as usize] = None;
        Ok(())
    }
}

impl LowerCtx for RegAlloc {
    fn resolve_vreg(
        &mut self,
        vreg: VReg,
        backend: &mut impl BackendEmitter,
    ) -> Result<ResolvedVReg, LowerError> {
        let width = self.vreg_width(vreg);
        let result = match &self.entry(vreg)?.loc {
            VRegLoc::Const(val) => ResolvedVReg::Const(*val, width),
            VRegLoc::Reg(preg) => ResolvedVReg::PReg(*preg, width),
            VRegLoc::Mem => {
                let slot = self.entry(vreg)?
                    .slots
                    .iter()
                    .find(|s| !s.dirty)
                    .map(|s| s.slot)
                    .ok_or(LowerError::UndefinedVReg(vreg))?;
                let preg = self.alloc_reg()?;
                backend.lower(self, IrInst::Load {
                    dst: preg,
                    width,
                    base: slot.base,
                    offset: slot.offset,
                })?;
                self.bindings[preg.0 as usize] = Some(vreg);
                self.entry_mut(vreg)?.loc = VRegLoc::Reg(preg);
                ResolvedVReg::PReg(preg, width)
            }
            VRegLoc::Pending => return Err(LowerError::UndefinedVReg(vreg)),
        };
        self.consume(vreg);
        Ok(result)
    }

    fn define_vreg(
        &mut self,
        vreg: VReg,
        backend: &mut impl BackendEmitter,
    ) -> Result<(PReg, Width), LowerError> {
        let width = self.vreg_width(vreg);
        let target = self.vreg_defs[vreg.0 as usize].target;
        match &self.entry(vreg)?.loc {
            VRegLoc::Pending => {
                let preg = match target {
                    Some(t) => self.acquire(t, backend)?,
                    None => self.alloc_reg()?,
                };
                self.bindings[preg.0 as usize] = Some(vreg);
                self.entry_mut(vreg)?.loc = VRegLoc::Reg(preg);
                Ok((preg, width))
            }
            VRegLoc::Reg(preg) => Ok((*preg, width)),
            _ => Err(LowerError::UnexpectedDefine(vreg)),
        }
    }

    fn alloc_reg(&mut self) -> Result<PReg, LowerError> {
        self.allocatable
            .iter()
            .find(|p| self.bindings[p.0 as usize].is_none())
            .copied()
            .ok_or(LowerError::RegPoolExhausted)
    }
}
