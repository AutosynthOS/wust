//! Register allocator — running state machine that tracks vreg
//! locations and manages physical register bindings.

use std::collections::HashMap;

use autosynth_ir::{IrInst, RegInst, SlotRef, VInit, VReg, VRegDef};
use autosynth_isa::{PReg, Width};
use autosynth_lower::{BackendEmitter, Emit, LowerCtx, LowerError, MachineConfig, ResolvedVReg};

#[derive(Debug, Clone, Copy)]
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

/// The mutable per-path state. Cloned for block snapshots.
#[derive(Clone)]
pub(crate) struct MachineState {
    entries: Vec<Option<VRegEntry>>,
    bindings: Vec<Option<VReg>>,
    remaining: HashMap<VReg, usize>,
    results: Vec<VReg>,
}

impl MachineState {
    pub(crate) fn new(num_vregs: usize, num_regs: usize) -> Self {
        Self {
            entries: vec![None; num_vregs],
            bindings: vec![None; num_regs],
            remaining: HashMap::new(),
            results: Vec::new(),
        }
    }

    pub(crate) fn begin_block(
        &mut self,
        remaining_uses: &HashMap<VReg, usize>,
        results: &std::collections::HashSet<VReg>,
    ) {
        self.remaining = remaining_uses.clone();
        self.results = results.iter().copied().collect();
    }
}

pub(crate) struct RegAlloc {
    config: MachineConfig,
    vreg_defs: Vec<VRegDef>,
    pub(crate) state: MachineState,
}

impl RegAlloc {
    pub(crate) fn new(config: &MachineConfig, vreg_defs: &[VRegDef]) -> Self {
        Self {
            config: config.clone(),
            vreg_defs: vreg_defs.to_vec(),
            state: MachineState::new(vreg_defs.len(), config.num_regs()),
        }
    }

    pub(crate) fn vreg_width(&self, vreg: VReg) -> Width {
        self.vreg_defs[vreg.0 as usize].width
    }

    fn entry(&self, vreg: VReg) -> Result<&VRegEntry, LowerError> {
        self.state.entries[vreg.0 as usize]
            .as_ref()
            .ok_or(LowerError::UndefinedVReg(vreg))
    }

    fn entry_mut(&mut self, vreg: VReg) -> Result<&mut VRegEntry, LowerError> {
        self.state.entries[vreg.0 as usize]
            .as_mut()
            .ok_or(LowerError::UndefinedVReg(vreg))
    }

    fn is_live(&self, vreg: VReg) -> bool {
        if self.state.results.contains(&vreg) {
            return true;
        }
        self.state.remaining.get(&vreg).map(|&n| n > 0).unwrap_or(false)
    }

    fn consume(&mut self, vreg: VReg) {
        if let Some(count) = self.state.remaining.get_mut(&vreg) {
            *count = count.saturating_sub(1);
        }
    }

    /// Allocate a register for a vreg, respecting its target constraint.
    fn alloc_for(
        &mut self,
        vreg: VReg,
        backend: &mut impl BackendEmitter,
    ) -> Result<PReg, LowerError> {
        let target = self.vreg_defs[vreg.0 as usize].target;
        let preg = match target {
            Some(t) => { self.acquire(t, backend)?; t }
            None => self.alloc_reg()?,
        };
        self.state.bindings[preg.0 as usize] = Some(vreg);
        Ok(preg)
    }

    /// Load a Mem vreg from a clean slot into a register (target-aware).
    fn reload(
        &mut self,
        vreg: VReg,
        backend: &mut impl BackendEmitter,
    ) -> Result<PReg, LowerError> {
        let width = self.vreg_width(vreg);
        let slot = self.entry(vreg)?
            .slots.iter().find(|s| !s.dirty).map(|s| s.slot)
            .ok_or(LowerError::UndefinedVReg(vreg))?;
        let preg = self.alloc_for(vreg, backend)?;
        backend.lower(self, IrInst::Load {
            dst: preg, width,
            base: slot.base, offset: slot.offset,
        }, Emit::Immediate)?;
        self.entry_mut(vreg)?.loc = VRegLoc::Reg(preg);
        Ok(preg)
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
                if self.state.entries[idx].is_some() {
                    return Err(LowerError::DuplicateDefine(*vreg));
                }
                let loc = match value {
                    VInit::Const(val) => VRegLoc::Const(*val),
                    VInit::PReg(preg) => {
                        self.acquire(*preg, backend)?;
                        self.state.bindings[preg.0 as usize] = Some(*vreg);
                        VRegLoc::Reg(*preg)
                    }
                    VInit::InstDst => VRegLoc::Pending,
                };
                self.state.entries[idx] = Some(VRegEntry {
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
                let loc = self.entry(*vreg)?.loc;
                let is_clean = self.entry(*vreg)?.slots.iter().any(|s| s.slot == *slot && !s.dirty);
                if matches!(loc, VRegLoc::Mem) && is_clean {
                    self.reload(*vreg, backend)?;
                }
                self.entry_mut(*vreg)?.slots.retain(|s| s.slot != *slot);
                Ok(())
            }
            RegInst::Clobber { vreg } => {
                backend.flush(self)?;
                let loc = self.entry(*vreg)?.loc;
                if let VRegLoc::Reg(preg) = loc {
                    let has_dirty = self.entry(*vreg)?.slots.iter().any(|s| s.dirty);
                    if has_dirty {
                        let width = self.vreg_width(*vreg);
                        self.flush_vreg(*vreg, preg, width, backend)?;
                    } else {
                        self.entry_mut(*vreg)?.loc = VRegLoc::Mem;
                        self.state.bindings[preg.0 as usize] = None;
                    }
                }
                Ok(())
            }
            RegInst::Resolve { vreg } => {
                self.define_vreg(*vreg, backend)?;
                Ok(())
            }
        }
    }

    // --- Eviction ---

    fn acquire(
        &mut self,
        preg: PReg,
        backend: &mut impl BackendEmitter,
    ) -> Result<PReg, LowerError> {
        let victim = match self.state.bindings[preg.0 as usize] {
            Some(v) => v,
            None => return Ok(preg),
        };

        let loc = self.entry(victim)?.loc;
        if !self.is_live(victim) || matches!(loc, VRegLoc::Const(_)) {
            self.state.bindings[preg.0 as usize] = None;
            return Ok(preg);
        }

        let width = self.vreg_width(victim);
        let has_remaining = self.state.remaining.get(&victim).map(|&n| n > 0).unwrap_or(false);
        if !has_remaining {
            self.flush_vreg(victim, preg, width, backend)?;
        } else {
            let dest = self.alloc_reg()?;
            backend.lower(self, IrInst::Move {
                dst: dest, dst_width: width,
                src: preg, src_width: width,
            }, Emit::Immediate)?;
            self.state.bindings[dest.0 as usize] = Some(victim);
            self.state.bindings[preg.0 as usize] = None;
            self.entry_mut(victim)?.loc = VRegLoc::Reg(dest);
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
            .slots.iter().find(|s| s.dirty).map(|s| s.slot)
            .ok_or(LowerError::UndefinedVReg(vreg))?;
        backend.lower(self, IrInst::Store {
            src: preg, width,
            base: slot.base, offset: slot.offset,
        }, Emit::Immediate)?;
        let entry = self.entry_mut(vreg)?;
        for s in &mut entry.slots {
            s.dirty = false;
        }
        entry.loc = VRegLoc::Mem;
        self.state.bindings[preg.0 as usize] = None;
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
        let loc = self.entry(vreg)?.loc;
        let result = match loc {
            VRegLoc::Const(val) => ResolvedVReg::Const(val, width),
            VRegLoc::Reg(preg) => ResolvedVReg::PReg(preg, width),
            VRegLoc::Mem => ResolvedVReg::PReg(self.reload(vreg, backend)?, width),
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
        let loc = self.entry(vreg)?.loc;
        match loc {
            VRegLoc::Pending => {
                let preg = self.alloc_for(vreg, backend)?;
                self.entry_mut(vreg)?.loc = VRegLoc::Reg(preg);
                Ok((preg, width))
            }
            VRegLoc::Reg(preg) => {
                if let Some(t) = self.vreg_defs[vreg.0 as usize].target {
                    if preg != t {
                        self.acquire(t, backend)?;
                        backend.flush(self)?;
                        backend.lower(self, IrInst::Move {
                            dst: t, dst_width: width,
                            src: preg, src_width: width,
                        }, Emit::Immediate)?;
                        self.state.bindings[t.0 as usize] = Some(vreg);
                        self.state.bindings[preg.0 as usize] = None;
                        self.entry_mut(vreg)?.loc = VRegLoc::Reg(t);
                        return Ok((t, width));
                    }
                }
                Ok((preg, width))
            }
            _ => Err(LowerError::UnexpectedDefine(vreg)),
        }
    }

    fn alloc_reg(&mut self) -> Result<PReg, LowerError> {
        let pool = self.config.scratch_pool();
        if let Some(&preg) = pool.iter().find(|p| self.state.bindings[p.0 as usize].is_none()) {
            return Ok(preg);
        }
        for &preg in pool {
            if let Some(vreg) = self.state.bindings[preg.0 as usize] {
                if !self.is_live(vreg) {
                    self.state.bindings[preg.0 as usize] = None;
                    return Ok(preg);
                }
            }
        }
        Err(LowerError::RegPoolExhausted)
    }
}
