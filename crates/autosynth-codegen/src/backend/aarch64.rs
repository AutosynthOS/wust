use std::collections::HashMap;

use autosynth_isa::Instruction;
use autosynth_isa_aarch64::{
    Aarch64Instruction, GprOrSp, GprOrZr, SImm9, StrPre, XGpr,
    reg::{Gpr, GprId},
};

use super::{BackendEmitter, PhysReg};
use crate::ir::Register;
use crate::ir::function::{IRFunction, IsaReg};
use crate::ir::instruction::IrInst;
use crate::ir::Value;

pub struct Aarch64Backend {
    pool: Vec<PhysReg>,
    assignments: HashMap<&'static str, PhysReg>,
}

impl Aarch64Backend {
    pub fn new() -> Self {
        // Full GP register pool. Excludes x18 (platform reserved on macOS/iOS)
        // and x31 (SP/ZR, not general purpose).
        let pool = (0u8..=30).filter(|&r| r != 18).map(PhysReg).collect();
        Self {
            pool,
            assignments: HashMap::new(),
        }
    }

    fn phys_to_xgpr(reg: PhysReg) -> XGpr {
        XGpr(GprId::from_index(reg.0))
    }

    fn reg_to_xgpr(reg: Register) -> XGpr {
        match reg {
            Register::Phys(n) => XGpr(GprId::from_index(n)),
            Register::Virtual(_) => todo!("virtual register lowering"),
        }
    }

    fn emit(code: &mut Vec<u8>, inst: impl autosynth_isa_aarch64::Aarch64Inst) {
        let mut buf = [0u8; 4];
        let n = Aarch64Instruction(inst)
            .encode(&mut buf)
            .expect("encode failed");
        code.extend_from_slice(&buf[..n]);
    }

    /// Map a fixed ISA role to its aarch64-specific physical register.
    fn fixed_phys(role: IsaReg) -> Option<PhysReg> {
        match role {
            IsaReg::FramePointer => Some(PhysReg(29)),
            IsaReg::StackPointer => Some(PhysReg(28)), // software SP (not hw SP)
            IsaReg::ReturnAddress => Some(PhysReg(30)),
            IsaReg::Define64(_) => None,
        }
    }

    /// Look up a named register that was previously reserved.
    pub fn get(&self, name: &str) -> PhysReg {
        self.assignments[name]
    }
}

impl BackendEmitter for Aarch64Backend {
    fn use_isa_reg(&mut self, name: &'static str, role: IsaReg) -> Register {
        let phys = if let Some(fixed) = Self::fixed_phys(role) {
            // Fixed role — remove from pool so Define64 can't reuse it.
            self.pool.retain(|r| *r != fixed);
            fixed
        } else {
            // Define64 — consume from remaining pool by index.
            let IsaReg::Define64(idx) = role else { unreachable!() };
            if idx >= 0 {
                self.pool.remove(idx as usize)
            } else {
                let i = self.pool.len().wrapping_add(idx as isize as usize);
                self.pool.remove(i)
            }
        };
        self.assignments.insert(name, phys);
        Register::Phys(phys.0)
    }

    fn scratch(&self) -> &[PhysReg] {
        &self.pool
    }

    fn lower(&self, func: &IRFunction) -> Vec<u8> {
        let mut code = Vec::new();

        for block in &func.blocks {
            for inst in &block.instructions {
                match inst {
                    IrInst::StackPush { def } => {
                        match def.value {
                            Value::Reg(reg) => {
                                let rt = Self::reg_to_xgpr(reg);

                                let base_reg =
                                    func.vstacks[def.slot.vstack.0 as usize].base;
                                let base = Self::reg_to_xgpr(base_reg);

                                let offset = -(def.slot.size as i16);
                                Self::emit(&mut code, StrPre {
                                    rt: GprOrZr::from(rt),
                                    rn: GprOrSp::from(Gpr::X(base)),
                                    imm: SImm9::new(offset).expect("push offset out of range"),
                                });
                            }
                            _ => {
                                // TODO: handle other push values (const, vreg)
                            }
                        }
                    }

                    IrInst::StackPop { .. } => {
                        // TODO
                    }

                    IrInst::Alu { .. }
                    | IrInst::Cmp { .. }
                    | IrInst::BrIf { .. }
                    | IrInst::Branch { .. }
                    | IrInst::Call { .. }
                    | IrInst::Return { .. } => {
                        // TODO
                    }
                }
            }
        }

        code
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CodeBuilder, FunctionBuilder, VStack};

    #[test]
    fn prologue_str_pre() {
        let mut backend = Aarch64Backend::new();

        let _lbp = backend.use_isa_reg("lbp", IsaReg::FramePointer);
        let lr = backend.use_isa_reg("lr", IsaReg::ReturnAddress);
        let fsp = backend.use_isa_reg("fsp", IsaReg::StackPointer);

        let mut f = FunctionBuilder::new();

        let fibre = f.define_vstack(VStack {
            base: fsp,
            offset: 0,
        });

        f.entry_block(crate::BlockId::Entry);
        f.push_i64(fibre, Value::Reg(lr));

        let mut cb = CodeBuilder::new();
        f.build(&mut cb);

        let func = &cb.functions()[0];
        let code = backend.lower(func);

        // str x30, [x28, #-8]!
        assert_eq!(code.len(), 4);
        let word = u32::from_le_bytes([code[0], code[1], code[2], code[3]]);

        // STR X30, [X28, #-8]! pre-index
        let expected = (0b11 << 30) | 0x38000C00 | (0x1F8 << 12) | (28 << 5) | 30;
        assert_eq!(word, expected, "got 0x{word:08X}, expected 0x{expected:08X}");
    }

    #[test]
    fn use_isa_reg_fixed_roles() {
        let mut backend = Aarch64Backend::new();

        let lbp = backend.use_isa_reg("lbp", IsaReg::FramePointer);
        let lr = backend.use_isa_reg("lr", IsaReg::ReturnAddress);
        let fsp = backend.use_isa_reg("fsp", IsaReg::StackPointer);

        assert_eq!(lbp, Register::Phys(29));
        assert_eq!(lr, Register::Phys(30));
        assert_eq!(fsp, Register::Phys(28));

        // Fixed regs removed from scratch pool
        let scratch = backend.scratch();
        assert!(!scratch.contains(&PhysReg(28)));
        assert!(!scratch.contains(&PhysReg(29)));
        assert!(!scratch.contains(&PhysReg(30)));
    }

    #[test]
    fn use_isa_reg_define64() {
        let mut backend = Aarch64Backend::new();

        // Reserve fixed roles first
        backend.use_isa_reg("lbp", IsaReg::FramePointer);
        backend.use_isa_reg("lr", IsaReg::ReturnAddress);
        backend.use_isa_reg("fsp", IsaReg::StackPointer);

        // After removing x28, x29, x30: pool = [0,1,...,17,19,...,27]
        let fuel = backend.use_isa_reg("fuel", IsaReg::Define64(0));
        // Define64(0) → first in remaining pool = x0
        assert_eq!(fuel, Register::Phys(0));

        let ctx = backend.use_isa_reg("ctx", IsaReg::Define64(-1));
        // After removing x0: pool = [1,...,17,19,...,27]
        // Define64(-1) → last = x27
        assert_eq!(ctx, Register::Phys(27));

        // Neither in scratch
        assert!(!backend.scratch().contains(&PhysReg(0)));
        assert!(!backend.scratch().contains(&PhysReg(27)));
    }

    #[test]
    fn no_pool_overlap() {
        let mut backend = Aarch64Backend::new();

        backend.use_isa_reg("lbp", IsaReg::FramePointer);
        backend.use_isa_reg("lr", IsaReg::ReturnAddress);
        backend.use_isa_reg("fsp", IsaReg::StackPointer);
        backend.use_isa_reg("fuel", IsaReg::Define64(0));
        backend.use_isa_reg("ctx", IsaReg::Define64(-1));

        // All assigned regs must not appear in scratch
        for (_, phys) in &backend.assignments {
            assert!(
                !backend.scratch().contains(phys),
                "assigned reg {phys:?} found in scratch pool"
            );
        }

        // Scratch pool has no duplicates
        let mut seen = std::collections::HashSet::new();
        for reg in backend.scratch() {
            assert!(seen.insert(reg), "duplicate in scratch pool: {reg:?}");
        }
    }
}
