//! Register allocator — running state machine that tracks vreg
//! locations and manages physical register bindings.

use std::collections::HashMap;

use autosynth_ir::{
    BlockId, IrInst, RegInst, SlotRef, VInit, VReg, VRegDef, VRegRef, VRegRefSource,
};
use autosynth_isa::{PReg, Width};
use autosynth_lower::{BackendEmitter, Emit, LowerCtx, LowerError, MachineConfig, ResolvedVReg};
use autosynth_lower::{trace, trace_ctx, trace_do};

// --- Types ---

#[derive(Debug, Clone, Copy)]
#[cfg_attr(feature = "trace", derive(serde::Serialize))]
enum VRegLoc {
    Const(i64),
    Pending,
    Reg(PReg),
    Mem,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "trace", derive(serde::Serialize))]
struct SlotState {
    slot: SlotRef,
    dirty: bool,
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "trace", derive(serde::Serialize))]
struct VRegEntry {
    loc: VRegLoc,
    slots: Vec<SlotState>,
}

/// The mutable per-path state. Cloned for block snapshots.
#[derive(Clone)]
#[cfg_attr(feature = "trace", derive(serde::Serialize))]
pub(crate) struct MachineState {
    def_entries: Vec<Option<VRegEntry>>,
    ref_entries: Vec<Option<VRegEntry>>,
    bindings: Vec<Option<VReg>>,
}

/// The register allocator. Immutable config + vreg_defs, mutable MachineState.
pub(crate) struct RegAlloc {
    config: MachineConfig,
    vreg_defs: Vec<VRegDef>,
    vreg_refs: Vec<VRegRef>,
    pub(crate) state: MachineState,
    /// Per-block remaining use counts for each vreg.
    /// `usize::MAX` for vregs needed by successor blocks.
    /// Cloned from `IrBlock.remaining_uses` at each `begin_block`.
    remaining_uses: HashMap<VReg, usize>,
}

// --- MachineState impl ---

impl MachineState {
    pub(crate) fn new(num_defs: usize, num_refs: usize, num_regs: usize) -> Self {
        Self {
            def_entries: vec![None; num_defs],
            ref_entries: vec![None; num_refs],
            bindings: vec![None; num_regs],
        }
    }

    fn entry(&self, vreg: VReg) -> Result<&VRegEntry, LowerError> {
        let table = match vreg {
            VReg::Def(id) => &self.def_entries[id as usize],
            VReg::Ref(id) => &self.ref_entries[id as usize],
        };
        table.as_ref().ok_or(LowerError::UndefinedVReg(vreg))
    }

    fn entry_mut(&mut self, vreg: VReg) -> Result<&mut VRegEntry, LowerError> {
        let table = match vreg {
            VReg::Def(id) => &mut self.def_entries[id as usize],
            VReg::Ref(id) => &mut self.ref_entries[id as usize],
        };
        table.as_mut().ok_or(LowerError::UndefinedVReg(vreg))
    }
}

// --- RegAlloc impl ---

impl RegAlloc {
    pub(crate) fn new(
        config: &MachineConfig,
        vreg_defs: &[VRegDef],
        vreg_refs: &[VRegRef],
    ) -> Self {
        Self {
            config: config.clone(),
            vreg_defs: vreg_defs.to_vec(),
            vreg_refs: vreg_refs.to_vec(),
            state: MachineState::new(vreg_defs.len(), vreg_refs.len(), config.num_regs()),
            remaining_uses: HashMap::new(),
        }
    }

    pub(crate) fn begin_block(&mut self, remaining_uses: &HashMap<VReg, usize>) {
        self.remaining_uses = remaining_uses.clone();
    }

    fn is_live(&self, vreg: VReg) -> bool {
        self.remaining_uses.get(&vreg).map(|&n| n > 0).unwrap_or(false)
    }

    fn consume(&mut self, vreg: VReg) {
        if let Some(count) = self.remaining_uses.get_mut(&vreg) {
            *count = count.saturating_sub(1);
        }
    }

    /// Resolve a VReg to its underlying Def, chasing through Direct refs.
    /// Phi refs are first-class and don't alias through.
    fn resolve_to_def(&self, vreg: VReg) -> VReg {
        autosynth_ir::resolve_ref(vreg, &self.vreg_refs)
    }

    pub(crate) fn vreg_width(&self, vreg: VReg) -> Width {
        match vreg {
            VReg::Def(id) => self.vreg_defs[id as usize].width,
            VReg::Ref(id) => self.vreg_refs[id as usize].width,
        }
    }

    fn alloc_for(
        &mut self,
        vreg: VReg,
        backend: &mut impl BackendEmitter,
    ) -> Result<PReg, LowerError> {
        let resolved = self.resolve_to_def(vreg);
        let VReg::Def(def_id) = resolved else {
            unreachable!()
        };
        let target = self.vreg_defs[def_id as usize].target;
        let preg = match target {
            Some(t) => {
                self.acquire(t, backend)?;
                t
            }
            None => self.alloc_reg()?,
        };
        self.state.bindings[preg.0 as usize] = Some(vreg);
        Ok(preg)
    }

    fn reload(
        &mut self,
        vreg: VReg,
        backend: &mut impl BackendEmitter,
    ) -> Result<PReg, LowerError> {
        trace_ctx!("origin", "regalloc");
        let width = self.vreg_width(vreg);
        let slot = self
            .state
            .entry(vreg)?
            .slots
            .iter()
            .find(|s| !s.dirty)
            .map(|s| s.slot)
            .ok_or(LowerError::UndefinedVReg(vreg))?;
        let preg = self.alloc_for(vreg, backend)?;
        backend.lower(
            self,
            IrInst::Load {
                dst: preg,
                width,
                base: slot.base,
                offset: slot.offset,
            },
            Emit::Immediate,
        )?;
        self.state.entry_mut(vreg)?.loc = VRegLoc::Reg(preg);
        Ok(preg)
    }

    // --- RegInst processing ---

    pub(crate) fn process(
        &mut self,
        inst: &RegInst,
        backend: &mut impl BackendEmitter,
    ) -> Result<(), LowerError> {
        let result = self.process_inner(inst, backend);
        trace_do! {
            let state_json = autosynth_lower::__serde_json::to_value(&self.state).unwrap();
            let inst_json = autosynth_lower::__serde_json::to_value(inst).unwrap();
            trace!({
                "type": "regalloc_state",
                "inst": inst_json,
                "state": state_json
            });
        }
        result
    }

    fn process_inner(
        &mut self,
        inst: &RegInst,
        backend: &mut impl BackendEmitter,
    ) -> Result<(), LowerError> {
        // Resolve any Ref VRegs to their underlying Def before processing.
        let inst = &match inst {
            RegInst::SetSlot { vreg, slot } => RegInst::SetSlot {
                vreg: self.resolve_to_def(*vreg),
                slot: *slot,
            },
            RegInst::ClearSlot { vreg, slot } => RegInst::ClearSlot {
                vreg: self.resolve_to_def(*vreg),
                slot: *slot,
            },
            RegInst::Clobber { vreg } => RegInst::Clobber {
                vreg: self.resolve_to_def(*vreg),
            },
            RegInst::Resolve { vreg } => RegInst::Resolve {
                vreg: self.resolve_to_def(*vreg),
            },
            other => other.clone(),
        };
        match inst {
            RegInst::Define { vreg, value } => {
                let VReg::Def(idx) = *vreg else {
                    panic!("RegInst::Define expects VReg::Def, got {vreg}");
                };
                let idx = idx as usize;
                if self.state.def_entries[idx].is_some() {
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
                self.state.def_entries[idx] = Some(VRegEntry {
                    loc,
                    slots: Vec::new(),
                });
                Ok(())
            }
            RegInst::SetSlot { vreg, slot } => {
                self.state.entry_mut(*vreg)?.slots.push(SlotState {
                    slot: *slot,
                    dirty: true,
                });
                Ok(())
            }
            RegInst::ClearSlot { vreg, slot } => {
                let loc = self.state.entry(*vreg)?.loc;
                let is_clean = self
                    .state
                    .entry(*vreg)?
                    .slots
                    .iter()
                    .any(|s| s.slot == *slot && !s.dirty);
                if matches!(loc, VRegLoc::Mem) && is_clean {
                    self.reload(*vreg, backend)?;
                }
                self.state
                    .entry_mut(*vreg)?
                    .slots
                    .retain(|s| s.slot != *slot);
                Ok(())
            }
            RegInst::Clobber { vreg } => {
                backend.flush(self)?;
                trace_ctx!("origin", "regalloc");
                let loc = self.state.entry(*vreg)?.loc;
                if let VRegLoc::Reg(preg) = loc {
                    let has_dirty = self.state.entry(*vreg)?.slots.iter().any(|s| s.dirty);
                    if has_dirty {
                        let width = self.vreg_width(*vreg);
                        self.flush_vreg(*vreg, preg, width, backend)?;
                    } else {
                        self.state.entry_mut(*vreg)?.loc = VRegLoc::Mem;
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

        let loc = self.state.entry(victim)?.loc;
        if !self.is_live(victim) || matches!(loc, VRegLoc::Const(_)) {
            self.state.bindings[preg.0 as usize] = None;
            return Ok(preg);
        }

        let width = self.vreg_width(victim);
        let remaining = self.remaining_uses.get(&victim).copied().unwrap_or(0);
        let used_again_in_block = remaining > 0 && remaining < usize::MAX;
        if !used_again_in_block {
            self.flush_vreg(victim, preg, width, backend)?;
        } else {
            let dest = self.alloc_reg()?;
            backend.lower(
                self,
                IrInst::Move {
                    dst: dest,
                    dst_width: width,
                    src: preg,
                    src_width: width,
                },
                Emit::Immediate,
            )?;
            self.state.bindings[dest.0 as usize] = Some(victim);
            self.state.bindings[preg.0 as usize] = None;
            self.state.entry_mut(victim)?.loc = VRegLoc::Reg(dest);
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
        let slot = self
            .state
            .entry(vreg)?
            .slots
            .iter()
            .find(|s| s.dirty)
            .map(|s| s.slot)
            .ok_or(LowerError::UndefinedVReg(vreg))?;
        backend.lower(
            self,
            IrInst::Store {
                src: preg,
                width,
                base: slot.base,
                offset: slot.offset,
            },
            Emit::Immediate,
        )?;
        let entry = self.state.entry_mut(vreg)?;
        for s in &mut entry.slots {
            s.dirty = false;
        }
        entry.loc = VRegLoc::Mem;
        self.state.bindings[preg.0 as usize] = None;
        Ok(())
    }

    /// Materialize phi ref values at a merge point.
    ///
    /// For each phi ref in `into_params`, finds this predecessor's source
    /// Def, ensures it's in a register, and creates a ref_entry for it.
    /// If `target` is Some, the phi must end up in the same register as
    /// the existing snapshot. If None, this predecessor defines the contract.
    pub(crate) fn converge_into(
        &mut self,
        from: BlockId,
        into_params: &std::collections::HashSet<VReg>,
        target: Option<&MachineState>,
        backend: &mut impl BackendEmitter,
    ) -> Result<(), LowerError> {
        for &param in into_params {
            let VReg::Ref(ref_id) = param else { continue };
            let VRegRefSource::Phi(sources) = &self.vreg_refs[ref_id as usize].source else {
                continue;
            };
            let Some((_, src_def)) = sources.iter().find(|(pred, _)| *pred == from) else {
                continue;
            };
            let src_def = self.resolve_to_def(*src_def);
            let width = self.vreg_width(src_def);

            trace!({
                "type": "converge",
                "parent": autosynth_lower::current_group(),
                "phi": format!("{param}"),
                "src": format!("{src_def}")
            });

            // Materialize the source into a register.
            let preg = match self.state.entry(src_def)?.loc {
                VRegLoc::Reg(preg) => preg,
                VRegLoc::Const(val) => {
                    let preg = self.alloc_for(src_def, backend)?;
                    self.state.entry_mut(src_def)?.loc = VRegLoc::Reg(preg);
                    backend.materialize_const(preg, val, width)?;
                    preg
                }
                VRegLoc::Mem => self.reload(src_def, backend)?,
                VRegLoc::Pending => return Err(LowerError::UndefinedVReg(src_def)),
            };

            // Create the phi ref's entry at this register.
            self.state.ref_entries[ref_id as usize] = Some(VRegEntry {
                loc: VRegLoc::Reg(preg),
                slots: Vec::new(),
            });
        }
        Ok(())
    }
}

// --- LowerCtx impl ---

impl LowerCtx for RegAlloc {
    fn resolve_vreg(
        &mut self,
        vreg: VReg,
        backend: &mut impl BackendEmitter,
    ) -> Result<ResolvedVReg, LowerError> {
        let vreg = self.resolve_to_def(vreg);
        let width = self.vreg_width(vreg);
        let loc = self.state.entry(vreg)?.loc;
        let result = match loc {
            VRegLoc::Const(val) => ResolvedVReg::Const(val, width),
            VRegLoc::Reg(preg) => ResolvedVReg::PReg(preg, width),
            VRegLoc::Mem => {
                trace!({"type": "reload", "vreg": format!("{vreg}")});
                ResolvedVReg::PReg(self.reload(vreg, backend)?, width)
            }
            VRegLoc::Pending => return Err(LowerError::UndefinedVReg(vreg)),
        };
        self.consume(vreg);
        trace_do! {
            let result_json = autosynth_lower::__serde_json::to_value(&result).unwrap();
            trace!({"type": "resolve_vreg", "vreg": format!("{vreg}"), "result": result_json});
        }
        Ok(result)
    }

    fn define_vreg(
        &mut self,
        vreg: VReg,
        backend: &mut impl BackendEmitter,
    ) -> Result<(PReg, Width), LowerError> {
        let width = self.vreg_width(vreg);
        let loc = self.state.entry(vreg)?.loc;
        match loc {
            VRegLoc::Pending => {
                let preg = self.alloc_for(vreg, backend)?;
                self.state.entry_mut(vreg)?.loc = VRegLoc::Reg(preg);
                trace!({"type": "define_vreg", "vreg": format!("{vreg}"), "preg": preg.0});
                Ok((preg, width))
            }
            VRegLoc::Reg(preg) => {
                let resolved = self.resolve_to_def(vreg);
                let VReg::Def(def_id) = resolved else {
                    unreachable!()
                };
                let target = self.vreg_defs[def_id as usize].target;
                if let Some(t) = target {
                    if preg != t {
                        self.acquire(t, backend)?;
                        backend.flush(self)?;
                        backend.lower(
                            self,
                            IrInst::Move {
                                dst: t,
                                dst_width: width,
                                src: preg,
                                src_width: width,
                            },
                            Emit::Immediate,
                        )?;
                        self.state.bindings[t.0 as usize] = Some(vreg);
                        self.state.bindings[preg.0 as usize] = None;
                        self.state.entry_mut(vreg)?.loc = VRegLoc::Reg(t);
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
        if let Some(preg) = pool
            .iter()
            .find(|p| self.state.bindings[p.0 as usize].is_none())
        {
            return Ok(*preg);
        }
        for &preg in &pool {
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
