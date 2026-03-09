//! Orchestrator — drives the backend emitter with register cache decisions.
//!
//! The orchestrator walks IR blocks, manages the register cache, and
//! calls the backend for instruction selection. It owns the code buffer
//! and all mutable compilation state.
//!
//! The orchestrator's job is simple: walk IR instructions, handle register
//! cache bookkeeping for stores/loads, and pass everything else to the backend.

mod regcache;

use std::collections::HashMap;

use autosynth_backend::{BackendEmitter, MachineConfig};
use autosynth_ir::{
    BlockId, CanonSlot, FunctionIdx, IRFunction, IrBlock, IrInst, Operand, Register, VReg, VRegDef,
    VStackConfig,
};
use autosynth_isa::{PReg, Width};
use autosynth_lower::LowerCtx;

use regcache::RegCache;

/// The orchestrator — implements [`LowerCtx`] for the backend.
///
/// Walks IR, manages the register cache, emits machine code. The backend
/// is passed into [`compile`](Self::compile) as a separate `&mut` so
/// there's no borrow conflict when calling `backend.lower(self, inst)`.
pub struct Orchestrator {
    /// Machine configuration — owned, immutable after construction.
    config: MachineConfig,
    /// Encoded instruction words.
    code: Vec<u8>,
    /// Register cache — tracks which vregs are in which physical registers.
    cache: RegCache,
    /// Per-vreg metadata, borrowed from the IRFunction.
    vreg_defs: Vec<VRegDef>,
    /// Virtual stack configs — needed to resolve canonical slot addresses for spills.
    vstacks: Vec<VStackConfig>,
    /// Block label → code offset (in words).
    labels: HashMap<BlockId, usize>,
}

impl Orchestrator {
    /// Create a new orchestrator from a pre-configured `MachineConfig`.
    ///
    /// The caller reserves registers via `config.reserve()` before
    /// passing it in. The remaining scratch pool is used for allocation.
    pub fn new(config: MachineConfig) -> Self {
        let cache = RegCache::new(config.scratch_pool());
        Self {
            config,
            code: Vec::with_capacity(64),
            cache,
            vreg_defs: Vec::new(),
            vstacks: Vec::new(),
            labels: HashMap::new(),
        }
    }

    /// The machine configuration (reserved registers, scratch pool).
    pub fn config(&self) -> &MachineConfig {
        &self.config
    }

    /// Compile an IR function into machine code bytes.
    ///
    /// The backend is passed separately so there's no borrow conflict
    /// when calling `backend.lower(self, inst)` — `self` is the LowerCtx
    /// and `backend` is a disjoint mutable reference.
    pub fn compile(
        &mut self,
        func: &IRFunction,
        backend: &mut impl BackendEmitter,
    ) -> Result<Vec<u8>, String> {
        self.vreg_defs = func.vreg_defs.clone();
        self.vstacks = func.vstacks.clone();

        let mut ir_index = 0;

        for block in &func.blocks {
            self.labels.insert(block.id, self.code.len());

            for inst in &block.instructions {
                autosynth_lower::dbg(|dbg| dbg.begin_ir_inst(ir_index));
                self.lower_inst(inst, func, backend)?;
                ir_index += 1;
            }

            backend.flush(self).map_err(|e| format!("{e}"))?;
        }

        backend.finalize(self).map_err(|e| format!("{e}"))?;

        Ok(self.to_bytes())
    }

    /// Dispatch a single IR instruction.
    ///
    /// The orchestrator only intercepts Store for register cache
    /// bookkeeping (param binds, const/alias skips, physical reg stores).
    /// Everything else passes straight through to the backend.
    fn lower_inst(
        &mut self,
        inst: &IrInst,
        func: &IRFunction,
        backend: &mut impl BackendEmitter,
    ) -> Result<(), String> {
        match inst {
            // VReg-source stores need cache bookkeeping (param binds,
            // const/alias skips). Everything else passes to the backend.
            IrInst::Store { src: src @ Operand::VReg(..), .. } => {
                self.lower_store(src, func, backend)
            }

            IrInst::Load {
                dst: Register::VReg(vreg, _),
                ..
            } => {
                // VReg loads are only real memory ops when the value isn't
                // already in the cache. If it's cached, skip the load.
                if self.cache.lookup(*vreg).is_some() {
                    return Ok(());
                }
                let def = &self.vreg_defs[vreg.0 as usize];
                if matches!(def.initial, Some(Operand::PReg(..))) {
                    backend
                        .lower(self, inst.clone())
                        .map_err(|e| format!("{e}"))
                } else {
                    Ok(())
                }
            }

            // After a call, all scratch registers are clobbered.
            IrInst::Call { .. } => {
                backend
                    .lower(self, inst.clone())
                    .map_err(|e| format!("{e}"))?;
                self.cache.invalidate_all();
                Ok(())
            }

            IrInst::Skipped(_) => Ok(()),

            _ => backend
                .lower(self, inst.clone())
                .map_err(|e| format!("{e}")),
        }
    }

    /// Handle a Store instruction (stack push) semantically.
    ///
    /// The meaning depends on the VRegDef's initial value:
    /// - PReg: bind the vreg to that physical register (params, LR stores)
    /// - ConstI32/I64: record as rematerializable, don't emit anything
    /// - VReg: alias — the new vreg shares the source's register
    /// - None: no-op (result written by a subsequent ALU/Call)
    fn lower_store(
        &mut self,
        src: &autosynth_ir::Operand,
        func: &IRFunction,
        backend: &mut impl BackendEmitter,
    ) -> Result<(), String> {
        let vreg = match src {
            autosynth_ir::Operand::VReg(v, _) => *v,
            _ => return Ok(()), // non-vreg stores handled elsewhere
        };
        let def = &self.vreg_defs[vreg.0 as usize];
        match def.initial {
            Some(Operand::PReg(preg, _)) => {
                self.cache.bind(vreg, preg);
            }
            Some(Operand::ConstI32(_) | Operand::ConstI64(_)) => {
                // Lazy: don't materialize yet. The regcache will handle it
                // when someone actually needs this vreg in a register.
            }
            Some(Operand::VReg(src, _)) => {
                // Transfer cache ownership: the destination vreg takes
                // over the source's register. This ensures eviction
                // spills to the destination's canonical slot (e.g. a
                // local slot), not the source's (e.g. an operand slot).
                if self.cache.lookup(src).is_some() {
                    self.cache.alias(vreg, src);
                    // Clear the VReg chain so that after cache
                    // invalidation, resolve_vreg loads from this vreg's
                    // own canonical slot instead of chaining to the
                    // source (whose slot may be on a different vstack).
                    self.vreg_defs[vreg.0 as usize].initial = None;
                }
            }
            None => {} // destination — written by subsequent instruction
        }
        Ok(())
    }

    /// Resolve a canonical slot to (base PReg, byte offset from base).
    fn slot_address(&self, slot: &CanonSlot) -> (PReg, u32) {
        let vstack = &self.vstacks[slot.vstack.0 as usize];
        let base_preg = match vstack.base {
            Register::PReg(preg, _) => preg,
            Register::VReg(_, _) => panic!("vstack base must be a physical register"),
        };
        (base_preg, slot.byte_offset)
    }

    /// Emit a spill store for an evicted dirty vreg via the backend.
    fn emit_eviction_store(
        &mut self,
        evicted_vreg: VReg,
        from_preg: PReg,
        backend: &mut impl BackendEmitter,
    ) -> Result<(), String> {
        let def = &self.vreg_defs[evicted_vreg.0 as usize];

        // Constants are rematerializable — no store needed.
        if matches!(
            def.initial,
            Some(Operand::ConstI32(_) | Operand::ConstI64(_))
        ) {
            return Ok(());
        }

        let slot = def.slot.as_ref().unwrap_or_else(|| {
            panic!("eviction of {evicted_vreg}: no canonical slot and not rematerializable")
        });
        let (base, offset) = self.slot_address(slot);
        backend
            .lower(
                self,
                IrInst::Store {
                    src: Operand::PReg(from_preg, def.width),
                    base,
                    offset,
                },
            )
            .map_err(|e| format!("{e}"))?;
        // Flush immediately — the store must land before the instruction
        // that overwrites the register (e.g. the sub that triggered eviction).
        backend.flush(self).map_err(|e| format!("{e}"))
    }

    fn to_bytes(&self) -> Vec<u8> {
        self.code.clone()
    }
}

impl LowerCtx for Orchestrator {
    fn const_value(&self, vreg: VReg) -> Option<i64> {
        let def = self.vreg_defs.get(vreg.0 as usize)?;
        match def.initial {
            Some(Operand::ConstI32(n)) => Some(n as i64),
            Some(Operand::ConstI64(n)) => Some(n),
            Some(Operand::VReg(src, _)) => self.const_value(src),
            _ => None,
        }
    }

    fn materialize_const(&mut self, _val: i64, width: Width) -> (PReg, Width) {
        todo!("materialize_const({_val}, {width})")
    }

    fn resolve_vreg(&mut self, vreg: VReg, backend: &mut impl BackendEmitter) -> (PReg, Width) {
        let def = self.vreg_defs[vreg.0 as usize];
        // If this vreg is already cached (e.g. via alias transfer), use it
        // directly — don't chain through to the source vreg.
        if let Some(preg) = self.cache.lookup(vreg) {
            return (preg, def.width);
        }
        // Follow VReg chain — aliases that weren't transferred (source
        // wasn't cached at store time) resolve through the chain.
        if let Some(Operand::VReg(src, _)) = def.initial {
            return self.resolve_vreg(src, backend);
        }
        let (preg, needs_load) = self.cache.ensure(vreg);
        if needs_load {
            let slot = def.slot.unwrap_or_else(|| {
                panic!("resolve_vreg: {vreg} needs load but has no canonical slot")
            });
            let (base, offset) = (
                match self.vstacks[slot.vstack.0 as usize].base {
                    Register::PReg(p, _) => p,
                    _ => panic!("vstack base must be a physical register"),
                },
                slot.byte_offset,
            );
            backend
                .lower(
                    self,
                    IrInst::Load {
                        dst: Register::PReg(preg, def.width),
                        base,
                        offset,
                    },
                )
                .expect("reload failed");
            backend.flush(self).expect("reload flush failed");
        }
        (preg, def.width)
    }

    fn define_vreg(&mut self, vreg: VReg, backend: &mut impl BackendEmitter) -> (PReg, Width) {
        let def = self.vreg_defs[vreg.0 as usize];
        let width = def.width;
        let preg = match def.target {
            Some(Register::PReg(target, _)) => {
                if let Some((evicted_vreg, dirty)) = self.cache.define_at(vreg, target) {
                    if dirty {
                        self.emit_eviction_store(evicted_vreg, target, backend)
                            .expect("eviction store failed");
                    }
                }
                target
            }
            Some(Register::VReg(src, _)) => {
                let src_preg = self
                    .cache
                    .lookup(src)
                    .unwrap_or_else(|| panic!("define_vreg: coalesce target {src} not in cache"));
                if let Some((evicted_vreg, dirty)) = self.cache.define_at(vreg, src_preg) {
                    if dirty {
                        self.emit_eviction_store(evicted_vreg, src_preg, backend)
                            .expect("eviction store failed");
                    }
                }
                src_preg
            }
            None => self.cache.define(vreg),
        };
        (preg, width)
    }

    fn emit_code(&mut self, bytes: &[u8]) -> usize {
        let offset = self.code.len();
        autosynth_lower::dbg(|dbg| dbg.set_machine("addr", &format!("{offset:04x}")));
        self.code.extend_from_slice(bytes);
        offset
    }

    fn patch_code(&mut self, offset: usize, bytes: &[u8]) {
        self.code[offset..offset + bytes.len()].copy_from_slice(bytes);
    }

    fn resolve_block(&self, block: BlockId) -> Option<usize> {
        self.labels.get(&block).copied()
    }

    fn resolve_func(&self, _func_idx: FunctionIdx) -> Option<usize> {
        // For now, all calls are self-recursive — function body starts at 0.
        Some(0)
    }
}
