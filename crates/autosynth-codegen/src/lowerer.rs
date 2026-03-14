//! Lowerer — drives the compile loop, delegating register allocation
//! to [`RegAlloc`] which implements [`LowerCtx`] directly.

use crate::ir_function::IRFunction;
use crate::regalloc::RegAlloc;
use autosynth_ir::LowerInst;
use autosynth_lower::{BackendEmitter, LowerError, MachineConfig};

pub struct Lowerer {
    regalloc: RegAlloc,
}

impl Lowerer {
    pub fn new(config: MachineConfig) -> Self {
        Self {
            regalloc: RegAlloc::new(config),
        }
    }

    pub fn compile(
        &mut self,
        func: &IRFunction,
        backend: &mut impl BackendEmitter,
    ) -> Result<Vec<u8>, LowerError> {
        self.regalloc.reset(func.vreg_defs.clone());
        let mut ir_index = 0;

        for &block_id in &func.block_order {
            let block = &func.blocks[&block_id];
            self.regalloc
                .begin_block(&block.remaining_uses, &block.results);

            for inst in &block.instructions {
                autosynth_lower::dbg(|dbg| dbg.begin_ir_inst(ir_index));
                match inst {
                    LowerInst::Ir(ir) => backend.lower(
                        &mut self.regalloc,
                        ir.clone(),
                        autosynth_lower::Emit::Fuse,
                    )?,
                    LowerInst::Reg(reg) => self.regalloc.process(reg, backend)?,
                }
                ir_index += 1;
            }

            backend.flush(&mut self.regalloc)?;
        }

        backend.finalize(&mut self.regalloc)?;

        Ok(vec![])
    }
}
