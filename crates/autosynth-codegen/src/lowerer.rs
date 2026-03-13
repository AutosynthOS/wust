//! Lowerer — drives the backend emitter with register cache decisions.
//!
//! Walks IR blocks, delegates register decisions to the VM snapshot,
//! and calls the backend for instruction selection. Owns the code
//! buffer and block label map.

use std::collections::HashMap;

use autosynth_ir::{BlockId, IrInst, LowerInst, RegInst, VReg, VRegDef};

use crate::ir_function::IRFunction;
use autosynth_isa::{PReg, Width};
use autosynth_lower::{BackendEmitter, LowerCtx, LowerError, MachineConfig, ResolvedVReg};

/// The lowerer — implements [`LowerCtx`] for the backend.
pub struct Lowerer {
    config: MachineConfig,
    code: Vec<u8>,
    /// Function-global vreg definitions, set at the start of compile().
    vreg_defs: Vec<VRegDef>,
    labels: HashMap<BlockId, usize>,
}

impl Lowerer {
    pub fn new(config: MachineConfig) -> Self {
        Self {
            config,
            code: Vec::with_capacity(64),
            vreg_defs: Vec::new(),
            labels: HashMap::new(),
        }
    }

    pub fn config(&self) -> &MachineConfig {
        &self.config
    }

    fn vreg_width(&self, vreg: VReg) -> Width {
        self.vreg_defs[vreg.0 as usize].width
    }

    /// Compile an IR function into machine code bytes.
    pub fn compile(
        &mut self,
        func: &IRFunction,
        backend: &mut impl BackendEmitter,
    ) -> Result<Vec<u8>, LowerError> {
        self.vreg_defs = func.vreg_defs.clone();
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
        // TODO: Call handling — process RegInst::Clobber + flush dirty
        // vregs before the call, then process RegInst::Bind for results
        // after. For now, just forward everything to the backend.
        backend.lower(self, inst.clone())
    }

    fn lower_reg(&mut self, inst: &RegInst) {
        // TODO: process RegInst to update per-vreg VRegState in the
        // register allocator. This is the new state machine:
        //   Define → creates vreg entry
        //   Bind { vreg, preg } → binds vreg to physical register
        //   SetSlot { vreg, slot } → assigns canonical slot
        //   ClearSlot { vreg } → removes canonical slot (pop)
        //   Clobber → marks all scratch registers as clobbered
        //   Use { vreg } → records a use for LRU tracking
        let _ = inst;
    }
}

impl LowerCtx for Lowerer {
    fn resolve_vreg(
        &mut self,
        vreg: VReg,
        _backend: &mut impl BackendEmitter,
    ) -> Result<ResolvedVReg, LowerError> {
        // TODO: implement proper resolution from VRegState.
        let width = self.vreg_width(vreg);
        Ok(ResolvedVReg::PReg(PReg(0), width))
    }

    fn define_vreg(&mut self, vreg: VReg, _backend: &mut impl BackendEmitter) -> (PReg, Width) {
        // TODO: implement proper allocation from VRegState.
        let width = self.vreg_width(vreg);
        (PReg(0), width)
    }

    fn alloc_scratch(&mut self, _width: Width) -> PReg {
        todo!("allocate a temp scratch register");
    }
}
