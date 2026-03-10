//! Orchestrator — drives the backend emitter with register cache decisions.
//!
//! Walks IR blocks, delegates register decisions to the cache, and
//! calls the backend for instruction selection. Owns the code buffer
//! and block label map.

use std::collections::HashMap;

use autosynth_ir::{BlockId, IRFunction, IrInst, VReg};
use autosynth_isa::{PReg, Width};
use autosynth_lower::{BackendEmitter, LowerCtx, LowerError, MachineConfig, ResolvedVReg};

use crate::regcache::{PendingStore, RegCache, ResolveResult};

/// The orchestrator — implements [`LowerCtx`] for the backend.
pub struct Orchestrator {
    config: MachineConfig,
    code: Vec<u8>,
    cache: RegCache,
    labels: HashMap<BlockId, usize>,
}

impl Orchestrator {
    pub fn new(config: MachineConfig) -> Self {
        let cache = RegCache::new(config.scratch_pool());
        Self {
            config,
            code: Vec::with_capacity(64),
            cache,
            labels: HashMap::new(),
        }
    }

    pub fn config(&self) -> &MachineConfig {
        &self.config
    }

    /// Compile an IR function into machine code bytes.
    pub fn compile(
        &mut self,
        func: &IRFunction,
        backend: &mut impl BackendEmitter,
    ) -> Result<Vec<u8>, LowerError> {
        self.cache.vreg_defs = func.vreg_defs.clone();
        self.cache.regions = func.regions.clone();

        let mut ir_index = 0;

        for block in &func.blocks {
            self.labels.insert(block.id, self.code.len());

            for inst in &block.instructions {
                autosynth_lower::dbg(|dbg| dbg.begin_ir_inst(ir_index));
                self.lower_inst(inst, backend)?;
                ir_index += 1;
            }

            backend.flush(self)?;
        }

        backend.finalize(self)?;

        Ok(self.code.clone())
    }

    fn lower_inst(
        &mut self,
        inst: &IrInst,
        backend: &mut impl BackendEmitter,
    ) -> Result<(), LowerError> {
        Ok(match inst {
            IrInst::Call { .. } => {
                // Cache decides what to flush, then invalidates.
                let stores = self.cache.prepare_call();
                for store in stores {
                    backend.lower(
                        self,
                        IrInst::Store {
                            src: store.src,
                            width: store.width,
                            base: store.base,
                            offset: store.offset,
                        },
                    )?;
                }
                backend.flush(self)?;
                backend.lower(self, inst.clone())?
            }
            _ => backend.lower(self, inst.clone())?,
        })
    }

    fn emit_eviction_store(
        &mut self,
        store: PendingStore,
        backend: &mut impl BackendEmitter,
    ) -> Result<(), String> {
        backend
            .lower(
                self,
                IrInst::Store {
                    src: store.src,
                    width: store.width,
                    base: store.base,
                    offset: store.offset,
                },
            )
            .map_err(|e| format!("{e}"))?;
        backend.flush(self).map_err(|e| format!("{e}"))
    }
}

impl LowerCtx for Orchestrator {
    fn resolve_vreg(
        &mut self,
        vreg: VReg,
        backend: &mut impl BackendEmitter,
    ) -> Result<ResolvedVReg, LowerError> {
        match self.cache.resolve(vreg) {
            ResolveResult::Ready(preg, w) => Ok(ResolvedVReg::PReg(preg, w)),
            ResolveResult::Load(preg, w, base, offset) => {
                backend.lower(
                    self,
                    IrInst::Load {
                        dst: preg,
                        width: w,
                        base,
                        offset,
                    },
                )?;
                backend.flush(self)?;
                Ok(ResolvedVReg::PReg(preg, w))
            }
            ResolveResult::Const(val, w) => Ok(ResolvedVReg::Const(val, w)),
        }
    }

    fn define_vreg(&mut self, vreg: VReg, backend: &mut impl BackendEmitter) -> (PReg, Width) {
        let (preg, width, eviction) = self.cache.define(vreg);
        if let Some(store) = eviction {
            self.emit_eviction_store(store, backend)
                .expect("eviction store failed");
        }
        (preg, width)
    }

    fn alloc_scratch(&mut self, _width: Width) -> PReg {
        todo!("allocate a temp scratch register");
    }
}
