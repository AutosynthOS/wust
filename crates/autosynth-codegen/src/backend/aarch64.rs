use std::collections::HashMap;

use autosynth_isa::Instruction;
use autosynth_isa_aarch64::{
    Aarch64Instruction, BCond, Cond, GprOrSp, GprOrZr, LdrPost, LdrUoff, Movz, OrrReg, Ret,
    SImm9, StrPre, StrUoff, SubsReg, UImm12, UImm16,
    reg::{Gpr, GprId, WGpr, XGpr},
};

use super::{BackendEmitter, PhysReg};
use crate::ir::block::BlockId;
use crate::ir::function::{IRFunction, IsaReg};
use crate::ir::instruction::{AluOp, CmpOp, IrInst};
use crate::ir::{IrType, Register, VReg, Value};
use crate::regalloc::RegCache;

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

    /// Look up a named register that was previously reserved.
    pub fn get(&self, name: &str) -> PhysReg {
        self.assignments[name]
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

    fn phys_to_wgpr(reg: PhysReg) -> WGpr {
        WGpr(GprId::from_index(reg.0))
    }

    fn phys_to_xgpr(reg: PhysReg) -> XGpr {
        XGpr(GprId::from_index(reg.0))
    }

    fn reg_to_xgpr(reg: Register) -> XGpr {
        match reg {
            Register::Phys(n) => XGpr(GprId::from_index(n)),
            Register::Virtual(_) => panic!("virtual register in lowering"),
        }
    }

    fn emit_inst(code: &mut Vec<u32>, inst: impl autosynth_isa_aarch64::Aarch64Inst) {
        code.push(inst.encode_word());
    }

    /// Map a CmpOp to the aarch64 condition code for the "true" branch.
    ///
    /// The Cmp instruction sets flags via `subs`. The condition code
    /// determines when the comparison result is truthy.
    fn cmp_op_to_cond(op: CmpOp) -> Cond {
        match op {
            CmpOp::Eq => Cond::EQ,
            CmpOp::Ne => Cond::NE,
            CmpOp::LtS => Cond::LT,
            CmpOp::LtU => Cond::CC,
            CmpOp::GtS => Cond::GT,
            CmpOp::GtU => Cond::HI,
            CmpOp::LeS => Cond::LE,
            CmpOp::LeU => Cond::LS,
            CmpOp::GeS => Cond::GE,
            CmpOp::GeU => Cond::CS,
        }
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
        let (bytes, _) = self.lower_with_disasm(func);
        bytes
    }
}

impl Aarch64Backend {
    /// Lower an IR function to machine code, also returning disassembly.
    pub fn lower_with_disasm(&self, func: &IRFunction) -> (Vec<u8>, String) {
        let mut ctx = LowerCtx::new(&self.pool, &func.vreg_defs);
        // Track which code offset each block starts at, for labeling.
        let mut block_labels: Vec<(usize, BlockId)> = Vec::new();

        for block in &func.blocks {
            block_labels.push((ctx.code.len(), block.id));
            ctx.labels.insert(block.id, ctx.code.len());

            if block.id != BlockId::Entry {
                ctx.cache.invalidate_all();
            }

            for inst in &block.instructions {
                ctx.lower_inst(inst, func);
            }
        }

        ctx.resolve_patches();

        // Build disasm listing with block labels interleaved.
        let mut listing = String::new();
        let mut label_idx = 0;
        for (i, asm) in ctx.disasm.iter().enumerate() {
            // Insert block label if this offset starts a new block.
            while label_idx < block_labels.len() && block_labels[label_idx].0 == i {
                listing.push_str(&format!("\n{:?}:\n", block_labels[label_idx].1));
                label_idx += 1;
            }
            listing.push_str(&format!("  {:04x} │ {:08x}  {asm}\n", i * 4, ctx.code[i]));
        }

        (ctx.to_bytes(), listing)
    }
}

/// Deferred comparison waiting for a BrIf to fuse into a conditional branch.
struct PendingCmp {
    cond: Cond,
}

/// Lowering context — mutable state for a single function's code generation.
struct LowerCtx<'a> {
    code: Vec<u32>,
    cache: RegCache,
    vreg_defs: &'a [crate::ir::VRegDef],
    labels: HashMap<BlockId, usize>,
    /// (code_offset, target_block) — patches for forward branches.
    patches: Vec<(usize, BlockId)>,
    /// Fused compare-and-branch state.
    pending_cmp: Option<PendingCmp>,
    /// Per-word disassembly annotations.
    disasm: Vec<String>,
}

impl<'a> LowerCtx<'a> {
    fn new(scratch: &[PhysReg], vreg_defs: &'a [crate::ir::VRegDef]) -> Self {
        Self {
            code: Vec::with_capacity(64),
            cache: RegCache::new(scratch),
            vreg_defs,
            labels: HashMap::new(),
            patches: Vec::new(),
            pending_cmp: None,
            disasm: Vec::new(),
        }
    }

    /// Emit an instruction and record its disassembly.
    fn emit<I: autosynth_isa_aarch64::Aarch64Inst + core::fmt::Display>(&mut self, inst: I) {
        self.disasm.push(format!("{inst}"));
        self.code.push(inst.encode_word());
    }

    /// Emit a raw word with a manual annotation.
    fn emit_raw(&mut self, word: u32, annotation: &str) {
        self.disasm.push(annotation.to_string());
        self.code.push(word);
    }

    /// Get the disassembly listing.
    pub fn disasm_listing(&self) -> String {
        let mut out = String::new();
        for (i, asm) in self.disasm.iter().enumerate() {
            out.push_str(&format!("{:04x} │ {:08x}  {asm}\n", i * 4, self.code[i]));
        }
        out
    }

    fn lower_inst(&mut self, inst: &IrInst, func: &IRFunction) {
        match inst {
            IrInst::StackPush { def } => {
                match def.value {
                    Value::Const(0) => {
                        // Placeholder for ALU/Cmp destination — skip.
                        // The ALU/Cmp instruction will define this VReg.
                    }
                    Value::ConstI32(n) => {
                        let phys = self.cache.define(def.id);
                        self.emit(Movz {
                            rd: GprOrZr::from(Aarch64Backend::phys_to_wgpr(phys)),
                            imm: UImm16::new(n as u16),
                            hw: 0,
                        });
                    }
                    Value::Const(n) => {
                        let phys = self.cache.define(def.id);
                        self.emit(Movz {
                            rd: GprOrZr::from(Aarch64Backend::phys_to_xgpr(phys)),
                            imm: UImm16::new(n as u16),
                            hw: 0,
                        });
                    }
                    Value::VReg(src) => {
                        // Ensure source is in a register (may emit a load).
                        let src_result = self.cache.ensure(src);
                        if src_result.needs_load {
                            self.emit_load(src, src_result.reg, func);
                        }
                        // Alias the new VReg to the same register (no mov).
                        // This works because ensure just placed src in the cache.
                        self.cache.alias(def.id, src)
                            .expect("alias failed after ensure");
                    }
                    Value::Reg(reg) => {
                        // Physical register push (e.g., fibre stack push of lr).
                        let base_reg = func.vstacks[def.slot.vstack.0 as usize].base;
                        let base = Aarch64Backend::reg_to_xgpr(base_reg);
                        let offset = -(def.slot.size as i16);
                        self.emit(StrPre {
                            rt: GprOrZr::from(Aarch64Backend::reg_to_xgpr(reg)),
                            rn: GprOrSp::from(Gpr::X(base)),
                            imm: SImm9::new(offset).expect("push offset out of range"),
                        });
                    }
                    Value::Param(_) => {
                        // Parameters arrive in calling convention registers.
                        // At function entry, param 0 is in x9, param 1 in x10, etc.
                        // The regcache doesn't need to emit code — just track the binding.
                        // TODO: bind param VRegs to calling convention regs
                    }
                }
            }

            IrInst::StackPop { def } => {
                // Special case: if this value was pushed from a physical
                // register (e.g., lr on fibre stack), pop it back to that
                // register using ldr_post.
                if let Value::Reg(reg) = def.value {
                    let base_reg = func.vstacks[def.slot.vstack.0 as usize].base;
                    let base = Aarch64Backend::reg_to_xgpr(base_reg);
                    self.emit(LdrPost {
                        rt: GprOrZr::from(Aarch64Backend::reg_to_xgpr(reg)),
                        rn: GprOrSp::from(Gpr::X(base)),
                        imm: SImm9::new(def.slot.size as i16)
                            .expect("pop offset out of range"),
                    });
                    return;
                }

                // If the VReg was never defined in the cache (e.g., Cmp
                // destination consumed by BrIf via flags), skip it.
                if self.cache.lookup(def.id).is_some() {
                    let result = self.cache.ensure(def.id);
                    if result.needs_load {
                        self.emit_load(def.id, result.reg, func);
                    }
                }
            }

            IrInst::Alu { op, dst, lhs, rhs } => {
                let lhs_result = self.cache.ensure(*lhs);
                if lhs_result.needs_load {
                    self.emit_load(*lhs, lhs_result.reg, func);
                }
                let rhs_result = self.cache.ensure(*rhs);
                if rhs_result.needs_load {
                    self.emit_load(*rhs, rhs_result.reg, func);
                }
                let dst_phys = self.cache.define(*dst);

                let lhs_ty = self.vreg_defs[lhs.0 as usize].ty;
                let is_32 = matches!(lhs_ty, IrType::I32 | IrType::F32);

                self.emit_alu(*op, dst_phys, lhs_result.reg, rhs_result.reg, is_32);
            }

            IrInst::Cmp { op, dst: _, lhs, rhs } => {
                // Emit subs wzr/xzr, lhs, rhs to set flags.
                // Don't define dst in regcache — BrIf will use the condition code.
                let lhs_result = self.cache.ensure(*lhs);
                if lhs_result.needs_load {
                    self.emit_load(*lhs, lhs_result.reg, func);
                }
                let rhs_result = self.cache.ensure(*rhs);
                if rhs_result.needs_load {
                    self.emit_load(*rhs, rhs_result.reg, func);
                }

                let lhs_ty = self.vreg_defs[lhs.0 as usize].ty;
                let is_32 = matches!(lhs_ty, IrType::I32 | IrType::F32);

                if is_32 {
                    self.emit(SubsReg {
                        rd: GprOrZr::Wzr,
                        rn: GprOrZr::from(Aarch64Backend::phys_to_wgpr(lhs_result.reg)),
                        rm: GprOrZr::from(Aarch64Backend::phys_to_wgpr(rhs_result.reg)),
                    });
                } else {
                    self.emit(SubsReg {
                        rd: GprOrZr::Xzr,
                        rn: GprOrZr::from(Aarch64Backend::phys_to_xgpr(lhs_result.reg)),
                        rm: GprOrZr::from(Aarch64Backend::phys_to_xgpr(rhs_result.reg)),
                    });
                }

                self.pending_cmp = Some(PendingCmp {
                    cond: Aarch64Backend::cmp_op_to_cond(*op),
                });
            }

            IrInst::BrIf { cond: _, block_if, block_else } => {
                // Fuse with pending comparison.
                let pending = self.pending_cmp.take()
                    .expect("BrIf without preceding Cmp");

                // Emit b.cond to the "if-true" block. The else block
                // is the fallthrough (next block in emission order).
                // We emit the *inverted* condition to branch to the else
                // block, since the then-block follows immediately.
                let else_offset = self.code.len();
                self.emit(BCond {
                    cond: pending.cond.invert(),
                    offset: 0, // patched later
                });
                self.patches.push((else_offset, *block_else));
            }

            IrInst::Branch { target } => {
                // Unconditional branch — emit b.al (always).
                let offset = self.code.len();
                self.emit(BCond {
                    cond: Cond::AL,
                    offset: 0,
                });
                self.patches.push((offset, *target));
            }

            IrInst::Return { values } => {
                // Move return value(s) to calling convention registers (x9, x10, ...).
                for (i, &vreg) in values.iter().enumerate() {
                    let result = self.cache.ensure(vreg);
                    if result.needs_load {
                        self.emit_load(vreg, result.reg, func);
                    }
                    let ret_reg = PhysReg(9 + i as u8);
                    if result.reg != ret_reg {
                        let ty = self.vreg_defs[vreg.0 as usize].ty;
                        let is_32 = matches!(ty, IrType::I32 | IrType::F32);
                        if is_32 {
                            self.emit(OrrReg {
                                rd: GprOrZr::from(Aarch64Backend::phys_to_wgpr(ret_reg)),
                                rn: GprOrZr::Wzr,
                                rm: GprOrZr::from(Aarch64Backend::phys_to_wgpr(result.reg)),
                            });
                        } else {
                            self.emit(OrrReg {
                                rd: GprOrZr::from(Aarch64Backend::phys_to_xgpr(ret_reg)),
                                rn: GprOrZr::Xzr,
                                rm: GprOrZr::from(Aarch64Backend::phys_to_xgpr(result.reg)),
                            });
                        }
                    }
                }

                // Emit ret (lr is assumed to be in x30 or restored from fibre stack).
                self.emit(Ret {
                    rn: XGpr(GprId::R30),
                });
            }

            IrInst::Call { func_idx: _ } => {
                // TODO: flush dirty regs, fuel check, frame advance, bl, restore
                // For now, emit a placeholder nop.
                self.emit_raw(0xD503201F, "nop  ; TODO: call stub");
                self.cache.invalidate_all();
            }
        }
    }

    /// Emit a load from a VReg's canonical stack slot.
    fn emit_load(&mut self, vreg: VReg, dst: PhysReg, func: &IRFunction) {
        let def = &self.vreg_defs[vreg.0 as usize];
        let vstack = &func.vstacks[def.slot.vstack.0 as usize];
        let base = Aarch64Backend::reg_to_xgpr(vstack.base);
        let offset = def.slot.byte_offset;

        match def.ty {
            IrType::I32 | IrType::F32 => {
                // ldr w{dst}, [x{base}, #offset]
                // Unsigned offset is in units of 4 bytes for 32-bit loads.
                self.emit(LdrUoff {
                    rt: GprOrZr::from(Aarch64Backend::phys_to_wgpr(dst)),
                    rn: GprOrSp::from(Gpr::X(base)),
                    offset: UImm12::new(offset as u16 / 4).expect("load offset out of range"),
                });
            }
            _ => {
                // ldr x{dst}, [x{base}, #offset]
                // Unsigned offset is in units of 8 bytes for 64-bit loads.
                self.emit(LdrUoff {
                    rt: GprOrZr::from(Aarch64Backend::phys_to_xgpr(dst)),
                    rn: GprOrSp::from(Gpr::X(base)),
                    offset: UImm12::new(offset as u16 / 8).expect("load offset out of range"),
                });
            }
        }
    }

    /// Emit an ALU instruction.
    fn emit_alu(&mut self, op: AluOp, dst: PhysReg, lhs: PhysReg, rhs: PhysReg, is_32: bool) {
        let (rd, rn, rm) = if is_32 {
            (
                GprOrZr::from(Aarch64Backend::phys_to_wgpr(dst)),
                GprOrZr::from(Aarch64Backend::phys_to_wgpr(lhs)),
                GprOrZr::from(Aarch64Backend::phys_to_wgpr(rhs)),
            )
        } else {
            (
                GprOrZr::from(Aarch64Backend::phys_to_xgpr(dst)),
                GprOrZr::from(Aarch64Backend::phys_to_xgpr(lhs)),
                GprOrZr::from(Aarch64Backend::phys_to_xgpr(rhs)),
            )
        };

        match op {
            AluOp::Add => {
                self.emit(autosynth_isa_aarch64::AddReg { rd, rn, rm });
            }
            AluOp::Sub => {
                self.emit(autosynth_isa_aarch64::SubReg { rd, rn, rm });
            }
            _ => {
                todo!("ALU op {:?} not yet lowered", op);
            }
        }
    }

    /// Resolve all forward branch patches.
    fn resolve_patches(&mut self) {
        for &(patch_offset, target) in &self.patches {
            let target_offset = self.labels.get(&target)
                .unwrap_or_else(|| panic!("unresolved label: {:?}", target));

            // Branch displacement in words (signed).
            let disp = *target_offset as i32 - patch_offset as i32;

            // Re-encode the b.cond instruction with the correct offset.
            let old_word = self.code[patch_offset];
            let cond_bits = old_word & 0xF;
            let imm19 = ((disp as u32) & 0x7FFFF) << 5;
            self.code[patch_offset] = 0x54000000 | imm19 | cond_bits;
        }
    }

    /// Convert the instruction buffer to bytes.
    fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(self.code.len() * 4);
        for &word in &self.code {
            bytes.extend_from_slice(&word.to_le_bytes());
        }
        bytes
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
