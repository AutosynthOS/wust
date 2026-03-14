//! Lowerer — drives the backend emitter with register cache decisions.
//!
//! Walks IR blocks, delegates register decisions to the VM snapshot,
//! and calls the backend for instruction selection. Owns the code
//! buffer and block label map.

use std::collections::HashMap;

use autosynth_ir::{BlockId, IrInst, LowerInst, RegInst, VInit, VReg, VRegDef};

use crate::ir_function::IRFunction;
use autosynth_isa::{PReg, Width};
use autosynth_lower::{BackendEmitter, LowerCtx, LowerError, MachineConfig, ResolvedVReg};

/// Where a vreg's value currently lives.
#[derive(Debug, Clone)]
enum VRegLoc {
    /// Compile-time constant — rematerialize on demand.
    Const(i64),
    /// Destination of a future instruction — no physical location yet.
    Pending,
    /// In a physical register.
    Reg(PReg),
}

/// The lowerer — implements [`LowerCtx`] for the backend.
pub struct Lowerer {
    config: MachineConfig,
    code: Vec<u8>,
    /// Function-global vreg definitions, set at the start of compile().
    vreg_defs: Vec<VRegDef>,
    /// Per-vreg location, indexed by VReg id.
    vreg_locs: Vec<Option<VRegLoc>>,
    labels: HashMap<BlockId, usize>,
}

impl Lowerer {
    pub fn new(config: MachineConfig) -> Self {
        Self {
            config,
            code: Vec::with_capacity(64),
            vreg_defs: Vec::new(),
            vreg_locs: Vec::new(),
            labels: HashMap::new(),
        }
    }

    pub fn config(&self) -> &MachineConfig {
        &self.config
    }

    fn vreg_width(&self, vreg: VReg) -> Width {
        self.vreg_defs[vreg.0 as usize].width
    }

    fn vreg_loc(&self, vreg: VReg) -> &VRegLoc {
        self.vreg_locs[vreg.0 as usize]
            .as_ref()
            .unwrap_or_else(|| panic!("vreg {vreg} has not been defined"))
    }

    fn vreg_loc_mut(&mut self, vreg: VReg) -> &mut VRegLoc {
        self.vreg_locs[vreg.0 as usize]
            .as_mut()
            .unwrap_or_else(|| panic!("vreg {vreg} has not been defined"))
    }

    /// Compile an IR function into machine code bytes.
    pub fn compile(
        &mut self,
        func: &IRFunction,
        backend: &mut impl BackendEmitter,
    ) -> Result<Vec<u8>, LowerError> {
        self.vreg_defs = func.vreg_defs.clone();
        self.vreg_locs = vec![None; func.vreg_defs.len()];
        let mut ir_index = 0;

        for &block_id in &func.block_order {
            self.labels.insert(block_id, self.code.len());
            let block = &func.blocks[&block_id];

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
        inst: &LowerInst,
        backend: &mut impl BackendEmitter,
    ) -> Result<(), LowerError> {
        match inst {
            LowerInst::Ir(ir) => self.lower_ir(ir, backend),
            LowerInst::Reg(reg) => {
                self.lower_reg(reg);
                Ok(())
            }
        }
    }

    fn lower_ir(
        &mut self,
        inst: &IrInst,
        backend: &mut impl BackendEmitter,
    ) -> Result<(), LowerError> {
        // TODO: Call handling — flush dirty vregs before the call.
        backend.lower(self, inst.clone())
    }

    fn lower_reg(&mut self, inst: &RegInst) {
        match inst {
            RegInst::Define { vreg, value } => {
                let idx = vreg.0 as usize;
                assert!(
                    self.vreg_locs[idx].is_none(),
                    "vreg {vreg} already defined"
                );
                self.vreg_locs[idx] = Some(match value {
                    VInit::Const(val) => VRegLoc::Const(*val),
                    VInit::PReg(preg) => VRegLoc::Reg(*preg),
                    VInit::InstDst => VRegLoc::Pending,
                });
            }
            // Slot bookkeeping — will matter for flush/eviction later.
            RegInst::SetSlot { .. } | RegInst::ClearSlot { .. } => {}
        }
    }
}

impl LowerCtx for Lowerer {
    fn resolve_vreg(
        &mut self,
        vreg: VReg,
        _backend: &mut impl BackendEmitter,
    ) -> Result<ResolvedVReg, LowerError> {
        let width = self.vreg_width(vreg);
        match self.vreg_loc(vreg) {
            VRegLoc::Const(val) => Ok(ResolvedVReg::Const(*val, width)),
            VRegLoc::Reg(preg) => Ok(ResolvedVReg::PReg(*preg, width)),
            VRegLoc::Pending => {
                panic!("resolve_vreg({vreg}): vreg is Pending — instruction not yet lowered")
            }
        }
    }

    fn define_vreg(&mut self, vreg: VReg, _backend: &mut impl BackendEmitter) -> (PReg, Width) {
        let width = self.vreg_width(vreg);
        match self.vreg_loc(vreg) {
            VRegLoc::Pending => {
                // TODO: allocate a real register from the free pool.
                let preg = PReg(0);
                *self.vreg_loc_mut(vreg) = VRegLoc::Reg(preg);
                (preg, width)
            }
            VRegLoc::Reg(preg) => {
                // Already in a register (e.g. PReg-origin vreg reused as dst).
                (*preg, width)
            }
            other => panic!("define_vreg({vreg}): unexpected state {other:?}"),
        }
    }

    fn alloc_scratch(&mut self, _width: Width) -> PReg {
        todo!("allocate a temp scratch register");
    }
}
