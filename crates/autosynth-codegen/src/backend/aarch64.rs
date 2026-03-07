use std::collections::HashMap;

use autosynth_isa_aarch64::{
    BCond, Cond, GprOrSp, GprOrZr, LdrPost, LdrUoff, Movz, OrrReg, Ret, SImm9, StrPre, StrUoff,
    SubsReg, UImm12, UImm16,
    reg::{Gpr, GprId, WGpr, XGpr},
};

use super::{BackendEmitter, PhysReg};
use crate::CodegenError;
use crate::disasm::{BlockLabel, BranchInfo, DisasmInst, DisasmMetadata};
use crate::ir::block::BlockId;
use crate::ir::function::{FunctionIdx, IRFunction, IsaReg};
use crate::ir::instruction::{AluOp, CmpOp, IrInst};
use crate::ir::{IrType, Register, VReg, VRegDef, Value};
use crate::regalloc::RegCache;

/// AArch64 backend: manages the ARM64 register pool and lowers IR to native machine code.
pub struct Aarch64Backend {
    pool: Vec<PhysReg>,
    assignments: HashMap<&'static str, PhysReg>,
}

impl Aarch64Backend {
    /// Create a new AArch64 backend with the full general-purpose register pool.
    pub fn new() -> Self {
        let pool = (0u8..=30).filter(|&r| r != 18).map(PhysReg).collect();
        Self { pool, assignments: HashMap::new() }
    }

    /// Look up a named register that was previously reserved.
    pub fn get(&self, name: &str) -> PhysReg { self.assignments[name] }

    fn fixed_phys(role: IsaReg) -> Option<PhysReg> {
        match role {
            IsaReg::FramePointer => Some(PhysReg(29)),
            IsaReg::StackPointer => Some(PhysReg(28)),
            IsaReg::ReturnAddress => Some(PhysReg(30)),
            IsaReg::Define64(_) => None,
        }
    }

    fn phys_to_wgpr(reg: PhysReg) -> WGpr { WGpr(GprId::from_index(reg.0)) }
    fn phys_to_xgpr(reg: PhysReg) -> XGpr { XGpr(GprId::from_index(reg.0)) }

    fn reg_to_xgpr(reg: Register) -> Result<XGpr, CodegenError> {
        match reg {
            Register::Phys(n) => Ok(XGpr(GprId::from_index(n))),
            Register::Virtual(v) => Err(CodegenError::InvalidRegister(
                format!("virtual register v{v} in lowering (expected physical)")
            )),
        }
    }

    fn cmp_op_to_cond(op: CmpOp) -> Cond {
        match op {
            CmpOp::Eq => Cond::EQ, CmpOp::Ne => Cond::NE,
            CmpOp::LtS => Cond::LT, CmpOp::LtU => Cond::CC,
            CmpOp::GtS => Cond::GT, CmpOp::GtU => Cond::HI,
            CmpOp::LeS => Cond::LE, CmpOp::LeU => Cond::LS,
            CmpOp::GeS => Cond::GE, CmpOp::GeU => Cond::CS,
        }
    }
}

impl BackendEmitter for Aarch64Backend {
    fn use_isa_reg(&mut self, name: &'static str, role: IsaReg) -> Register {
        let phys = if let Some(fixed) = Self::fixed_phys(role) {
            self.pool.retain(|r| *r != fixed);
            fixed
        } else {
            let IsaReg::Define64(idx) = role else { unreachable!() };
            if idx >= 0 { self.pool.remove(idx as usize) }
            else {
                let i = self.pool.len().wrapping_add(idx as isize as usize);
                self.pool.remove(i)
            }
        };
        self.assignments.insert(name, phys);
        Register::Phys(phys.0)
    }

    fn scratch(&self) -> &[PhysReg] { &self.pool }

    fn lower(&self, func: &IRFunction) -> Result<Vec<u8>, CodegenError> {
        let (bytes, _) = self.lower_with_disasm(func)?;
        Ok(bytes)
    }
}

impl Aarch64Backend {
    /// Lower an IR function to machine code bytes and structured disassembly metadata.
    pub fn lower_with_disasm(&self, func: &IRFunction) -> Result<(Vec<u8>, DisasmMetadata), CodegenError> {
        let mut ctx = LowerCtx::new(&self.pool, &func.vreg_defs);
        let mut block_labels: Vec<BlockLabel> = Vec::new();

        for block in &func.blocks {
            block_labels.push(BlockLabel { offset: ctx.code.len() * 4, id: block.id, name: None });
            ctx.labels.insert(block.id, ctx.code.len());
            if block.id != BlockId::Entry { ctx.cache.invalidate_all(); }
            for inst in &block.instructions { ctx.lower_inst(inst, func)?; }
        }

        ctx.resolve_patches()?;

        let instructions: Vec<DisasmInst> = ctx.disasm.iter().enumerate()
            .map(|(i, asm)| DisasmInst { offset: i * 4, text: asm.clone(), annotation: None })
            .collect();
        let branches = detect_branches(&ctx.code);
        let meta = DisasmMetadata { instructions, block_labels, branches, signature: None };
        Ok((ctx.to_bytes(), meta))
    }
}

struct PendingCmp { cond: Cond }

struct LowerCtx<'a> {
    code: Vec<u32>,
    cache: RegCache,
    vreg_defs: &'a [VRegDef],
    labels: HashMap<BlockId, usize>,
    patches: Vec<(usize, BlockId)>,
    pending_cmp: Option<PendingCmp>,
    disasm: Vec<String>,
}

impl<'a> LowerCtx<'a> {
    fn new(scratch: &[PhysReg], vreg_defs: &'a [VRegDef]) -> Self {
        Self {
            code: Vec::with_capacity(64), cache: RegCache::new(scratch), vreg_defs,
            labels: HashMap::new(), patches: Vec::new(), pending_cmp: None, disasm: Vec::new(),
        }
    }

    fn emit<I: autosynth_isa_aarch64::Aarch64Inst + core::fmt::Display>(&mut self, inst: I) {
        self.disasm.push(format!("{inst}"));
        self.code.push(inst.encode_word());
    }

    fn resolve(&mut self, reg: Register, func: &IRFunction) -> Result<PhysReg, CodegenError> {
        match reg {
            Register::Phys(n) => Ok(PhysReg(n)),
            Register::Virtual(id) => {
                let vreg = VReg(id);
                let result = self.cache.ensure(vreg)?;
                if result.needs_load { self.emit_load(vreg, result.reg, func)?; }
                Ok(result.reg)
            }
        }
    }

    fn resolve_dst(&mut self, reg: Register) -> Result<PhysReg, CodegenError> {
        match reg {
            Register::Phys(n) => Ok(PhysReg(n)),
            Register::Virtual(id) => self.cache.define(VReg(id)),
        }
    }

    fn reg_type(&self, reg: Register) -> IrType {
        match reg {
            Register::Phys(_) => IrType::I64,
            Register::Virtual(id) => self.vreg_defs[id as usize].ty,
        }
    }

    fn try_const(&self, reg: Register) -> Option<i64> {
        match reg {
            Register::Phys(_) => None,
            Register::Virtual(id) => match self.vreg_defs[id as usize].value {
                Value::ConstI32(n) => Some(n as i64),
                Value::Const(n) => Some(n),
                _ => None,
            },
        }
    }

    fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(self.code.len() * 4);
        for &word in &self.code { bytes.extend_from_slice(&word.to_le_bytes()); }
        bytes
    }

    /// Dispatch an IR instruction to the appropriate lowering helper.
    fn lower_inst(&mut self, inst: &IrInst, func: &IRFunction) -> Result<(), CodegenError> {
        match inst {
            IrInst::StackPush { def } => self.lower_stack_push(def, func),
            IrInst::StackPop { def } => self.lower_stack_pop(def, func),
            IrInst::Alu { op, dst, lhs, rhs } => self.lower_alu(*op, *dst, *lhs, *rhs, func),
            IrInst::Cmp { op, dst: _, lhs, rhs } => self.lower_cmp(*op, *lhs, *rhs, func),
            IrInst::BrIf { cond: _, block_if: _, block_else } => self.lower_br_if(*block_else),
            IrInst::Branch { target } => self.lower_branch(*target),
            IrInst::Call { func_idx, args, results, frame_advance } => self.lower_call(func_idx, args, results, *frame_advance, func),
            IrInst::Return { values } => self.lower_return(values, func),
        }
    }

    fn lower_stack_push(&mut self, def: &VRegDef, func: &IRFunction) -> Result<(), CodegenError> {
        match def.value {
            Value::Const(0) => {}
            Value::ConstI32(n) => {
                let phys = self.cache.define(def.id)?;
                self.emit(Movz { rd: GprOrZr::from(Aarch64Backend::phys_to_wgpr(phys)), imm: UImm16::new(n as u16), hw: 0 });
            }
            Value::Const(n) => {
                let phys = self.cache.define(def.id)?;
                self.emit(Movz { rd: GprOrZr::from(Aarch64Backend::phys_to_xgpr(phys)), imm: UImm16::new(n as u16), hw: 0 });
            }
            Value::VReg(src) => {
                let src_result = self.cache.ensure(src)?;
                if src_result.needs_load { self.emit_load(src, src_result.reg, func)?; }
                self.cache.alias(def.id, src).expect("alias failed after ensure");
            }
            Value::Reg(reg) => {
                let base_reg = func.vstacks[def.slot.vstack.0 as usize].base;
                let base = Aarch64Backend::reg_to_xgpr(base_reg)?;
                let offset = -(def.slot.size as i16);
                let imm = SImm9::new(offset).map_err(|_| CodegenError::OffsetOutOfRange { offset: offset as u32, max: 255 })?;
                self.emit(StrPre { rt: GprOrZr::from(Aarch64Backend::reg_to_xgpr(reg)?), rn: GprOrSp::from(Gpr::X(base)), imm });
            }
            Value::Param(i) => {
                // Parameters arrive in calling convention registers (x9, x10, ...).
                let cc_reg = PhysReg(9 + i as u8);
                self.cache.bind(def.id, cc_reg);
            }
        }
        Ok(())
    }

    fn lower_stack_pop(&mut self, def: &VRegDef, func: &IRFunction) -> Result<(), CodegenError> {
        if let Value::Reg(reg) = def.value {
            let base_reg = func.vstacks[def.slot.vstack.0 as usize].base;
            let base = Aarch64Backend::reg_to_xgpr(base_reg)?;
            let imm = SImm9::new(def.slot.size as i16)
                .map_err(|_| CodegenError::OffsetOutOfRange { offset: def.slot.size as u32, max: 255 })?;
            self.emit(LdrPost { rt: GprOrZr::from(Aarch64Backend::reg_to_xgpr(reg)?), rn: GprOrSp::from(Gpr::X(base)), imm });
            return Ok(());
        }
        if self.cache.lookup(def.id).is_some() {
            let result = self.cache.ensure(def.id)?;
            if result.needs_load { self.emit_load(def.id, result.reg, func)?; }
        }
        Ok(())
    }

    fn lower_alu(&mut self, op: AluOp, dst: Register, lhs: Register, rhs: Register, func: &IRFunction) -> Result<(), CodegenError> {
        let lhs_phys = self.resolve(lhs, func)?;
        let dst_phys = self.resolve_dst(dst)?;
        let is_32 = matches!(self.reg_type(lhs), IrType::I32 | IrType::F32);
        if let Some(imm) = self.try_const(rhs) {
            if let Ok(imm12) = UImm12::new(imm as u16) {
                self.emit_alu_imm(op, dst_phys, lhs_phys, imm12, is_32);
                if let Register::Virtual(id) = rhs { self.cache.release(VReg(id)); }
                return Ok(());
            }
        }
        let rhs_phys = self.resolve(rhs, func)?;
        self.emit_alu_reg(op, dst_phys, lhs_phys, rhs_phys, is_32);
        Ok(())
    }

    fn lower_cmp(&mut self, op: CmpOp, lhs: Register, rhs: Register, func: &IRFunction) -> Result<(), CodegenError> {
        let lhs_phys = self.resolve(lhs, func)?;
        let rhs_phys = self.resolve(rhs, func)?;
        let is_32 = matches!(self.reg_type(lhs), IrType::I32 | IrType::F32);
        if is_32 {
            self.emit(SubsReg { rd: GprOrZr::Wzr, rn: GprOrZr::from(Aarch64Backend::phys_to_wgpr(lhs_phys)), rm: GprOrZr::from(Aarch64Backend::phys_to_wgpr(rhs_phys)) });
        } else {
            self.emit(SubsReg { rd: GprOrZr::Xzr, rn: GprOrZr::from(Aarch64Backend::phys_to_xgpr(lhs_phys)), rm: GprOrZr::from(Aarch64Backend::phys_to_xgpr(rhs_phys)) });
        }
        self.pending_cmp = Some(PendingCmp { cond: Aarch64Backend::cmp_op_to_cond(op) });
        Ok(())
    }

    fn lower_br_if(&mut self, block_else: BlockId) -> Result<(), CodegenError> {
        let pending = self.pending_cmp.take().expect("BrIf without preceding Cmp");
        let else_offset = self.code.len();
        self.emit(BCond { cond: pending.cond.invert(), offset: 0 });
        self.patches.push((else_offset, block_else));
        Ok(())
    }

    fn lower_branch(&mut self, target: BlockId) -> Result<(), CodegenError> {
        let offset = self.code.len();
        self.emit(BCond { cond: Cond::AL, offset: 0 });
        self.patches.push((offset, target));
        Ok(())
    }

    fn lower_call(&mut self, func_idx: &FunctionIdx, args: &[VReg], results: &[VReg], frame_advance: u32, func: &IRFunction) -> Result<(), CodegenError> {
        // Flush ALL dirty registers first, before any arg moves that might
        // overwrite registers holding live values (e.g. local $a in w9 would
        // be clobbered if we moved a new arg to w9 before flushing).
        let dirty = self.cache.flush_dirty();
        for (phys, vreg) in dirty { self.emit_store(vreg, phys, func)?; }

        // Move arguments into calling convention registers (x9, x10, ...).
        for (i, &arg) in args.iter().enumerate() {
            let r = self.cache.ensure(arg)?;
            if r.needs_load { self.emit_load(arg, r.reg, func)?; }
            let cc_reg = PhysReg(9 + i as u8);
            if r.reg != cc_reg {
                let ty = self.vreg_defs[arg.0 as usize].ty;
                let is_32 = matches!(ty, IrType::I32 | IrType::F32);
                self.emit_mov(cc_reg, r.reg, is_32);
            }
        }

        // Advance frame pointer: lbp += frame_advance
        if frame_advance > 0 {
            let imm = UImm12::new(frame_advance as u16)
                .map_err(|_| CodegenError::OffsetOutOfRange { offset: frame_advance, max: 4095 })?;
            let fp = GprOrSp::from(Gpr::X(XGpr(GprId::R29)));
            self.emit(autosynth_isa_aarch64::AddImm { rd: fp, rn: fp, imm });
        }

        // Store args to the callee's frame (x29 now points to callee's locals_base).
        // The body reads params from memory at [x29, #offset], so we must ensure
        // the calling convention register values are written to the callee's local slots.
        let mut param_offset = 0u32;
        for (i, &arg) in args.iter().enumerate() {
            let cc_reg = PhysReg(9 + i as u8);
            let ty = self.vreg_defs[arg.0 as usize].ty;
            match ty {
                IrType::I32 | IrType::F32 => {
                    let uimm = UImm12::new(param_offset as u16 / 4)
                        .map_err(|_| CodegenError::OffsetOutOfRange { offset: param_offset, max: 4095 * 4 })?;
                    self.emit(StrUoff {
                        rt: GprOrZr::from(Aarch64Backend::phys_to_wgpr(cc_reg)),
                        rn: GprOrSp::from(Gpr::X(XGpr(GprId::R29))),
                        offset: uimm,
                    });
                    param_offset += 4;
                }
                _ => {
                    let uimm = UImm12::new(param_offset as u16 / 8)
                        .map_err(|_| CodegenError::OffsetOutOfRange { offset: param_offset, max: 4095 * 8 })?;
                    self.emit(StrUoff {
                        rt: GprOrZr::from(Aarch64Backend::phys_to_xgpr(cc_reg)),
                        rn: GprOrSp::from(Gpr::X(XGpr(GprId::R29))),
                        offset: uimm,
                    });
                    param_offset += 8;
                }
            }
        }

        let FunctionIdx::User(_idx) = func_idx;
        let entry_offset = self.labels.get(&BlockId::Entry).copied().unwrap_or(0);
        let disp = entry_offset as i32 - self.code.len() as i32;
        self.emit(autosynth_isa_aarch64::Bl { offset: disp });

        // Restore frame pointer: lbp -= frame_advance
        if frame_advance > 0 {
            let imm = UImm12::new(frame_advance as u16)
                .map_err(|_| CodegenError::OffsetOutOfRange { offset: frame_advance, max: 4095 })?;
            let fp = GprOrSp::from(Gpr::X(XGpr(GprId::R29)));
            self.emit(autosynth_isa_aarch64::SubImm { rd: fp, rn: fp, imm });
        }

        // After call, all registers are clobbered.
        self.cache.invalidate_all();

        // Bind return values from calling convention registers (dirty,
        // because the value has never been stored to its canonical slot).
        for (i, &res) in results.iter().enumerate() {
            let cc_reg = PhysReg(9 + i as u8);
            self.cache.bind_dirty(res, cc_reg);
        }
        Ok(())
    }

    fn lower_return(&mut self, values: &[VReg], func: &IRFunction) -> Result<(), CodegenError> {
        for (i, &vreg) in values.iter().enumerate() {
            let result = self.cache.ensure(vreg)?;
            if result.needs_load { self.emit_load(vreg, result.reg, func)?; }
            let ret_reg = PhysReg(9 + i as u8);
            if result.reg != ret_reg {
                let ty = self.vreg_defs[vreg.0 as usize].ty;
                let is_32 = matches!(ty, IrType::I32 | IrType::F32);
                self.emit_mov(ret_reg, result.reg, is_32);
            }
        }
        self.emit(Ret { rn: XGpr(GprId::R30) });
        Ok(())
    }

    fn emit_mov(&mut self, dst: PhysReg, src: PhysReg, is_32: bool) {
        if is_32 {
            self.emit(OrrReg { rd: GprOrZr::from(Aarch64Backend::phys_to_wgpr(dst)), rn: GprOrZr::Wzr, rm: GprOrZr::from(Aarch64Backend::phys_to_wgpr(src)) });
        } else {
            self.emit(OrrReg { rd: GprOrZr::from(Aarch64Backend::phys_to_xgpr(dst)), rn: GprOrZr::Xzr, rm: GprOrZr::from(Aarch64Backend::phys_to_xgpr(src)) });
        }
    }

    fn emit_load(&mut self, vreg: VReg, dst: PhysReg, func: &IRFunction) -> Result<(), CodegenError> {
        let def = &self.vreg_defs[vreg.0 as usize];
        let vstack = &func.vstacks[def.slot.vstack.0 as usize];
        let base = Aarch64Backend::reg_to_xgpr(vstack.base)?;
        let offset = def.slot.byte_offset;
        match def.ty {
            IrType::I32 | IrType::F32 => {
                let uimm = UImm12::new(offset as u16 / 4).map_err(|_| CodegenError::OffsetOutOfRange { offset: offset as u32, max: 4095 * 4 })?;
                self.emit(LdrUoff { rt: GprOrZr::from(Aarch64Backend::phys_to_wgpr(dst)), rn: GprOrSp::from(Gpr::X(base)), offset: uimm });
            }
            _ => {
                let uimm = UImm12::new(offset as u16 / 8).map_err(|_| CodegenError::OffsetOutOfRange { offset: offset as u32, max: 4095 * 8 })?;
                self.emit(LdrUoff { rt: GprOrZr::from(Aarch64Backend::phys_to_xgpr(dst)), rn: GprOrSp::from(Gpr::X(base)), offset: uimm });
            }
        }
        Ok(())
    }

    fn emit_store(&mut self, vreg: VReg, src: PhysReg, func: &IRFunction) -> Result<(), CodegenError> {
        let def = &self.vreg_defs[vreg.0 as usize];
        let vstack = &func.vstacks[def.slot.vstack.0 as usize];
        let base = Aarch64Backend::reg_to_xgpr(vstack.base)?;
        let offset = def.slot.byte_offset;
        match def.ty {
            IrType::I32 | IrType::F32 => {
                let uimm = UImm12::new(offset as u16 / 4).map_err(|_| CodegenError::OffsetOutOfRange { offset: offset as u32, max: 4095 * 4 })?;
                self.emit(StrUoff { rt: GprOrZr::from(Aarch64Backend::phys_to_wgpr(src)), rn: GprOrSp::from(Gpr::X(base)), offset: uimm });
            }
            _ => {
                let uimm = UImm12::new(offset as u16 / 8).map_err(|_| CodegenError::OffsetOutOfRange { offset: offset as u32, max: 4095 * 8 })?;
                self.emit(StrUoff { rt: GprOrZr::from(Aarch64Backend::phys_to_xgpr(src)), rn: GprOrSp::from(Gpr::X(base)), offset: uimm });
            }
        }
        Ok(())
    }

    fn emit_alu_reg(&mut self, op: AluOp, dst: PhysReg, lhs: PhysReg, rhs: PhysReg, is_32: bool) {
        let (rd, rn, rm) = if is_32 {
            (GprOrZr::from(Aarch64Backend::phys_to_wgpr(dst)), GprOrZr::from(Aarch64Backend::phys_to_wgpr(lhs)), GprOrZr::from(Aarch64Backend::phys_to_wgpr(rhs)))
        } else {
            (GprOrZr::from(Aarch64Backend::phys_to_xgpr(dst)), GprOrZr::from(Aarch64Backend::phys_to_xgpr(lhs)), GprOrZr::from(Aarch64Backend::phys_to_xgpr(rhs)))
        };
        match op {
            AluOp::Add => self.emit(autosynth_isa_aarch64::AddReg { rd, rn, rm }),
            AluOp::Sub => self.emit(autosynth_isa_aarch64::SubReg { rd, rn, rm }),
            _ => todo!("ALU op {:?} not yet lowered", op),
        }
    }

    fn emit_alu_imm(&mut self, op: AluOp, dst: PhysReg, src: PhysReg, imm: UImm12, is_32: bool) {
        let (rd, rn) = if is_32 {
            (GprOrSp::from(Aarch64Backend::phys_to_wgpr(dst)), GprOrSp::from(Aarch64Backend::phys_to_wgpr(src)))
        } else {
            (GprOrSp::from(Gpr::X(Aarch64Backend::phys_to_xgpr(dst))), GprOrSp::from(Gpr::X(Aarch64Backend::phys_to_xgpr(src))))
        };
        match op {
            AluOp::Add => self.emit(autosynth_isa_aarch64::AddImm { rd, rn, imm }),
            AluOp::Sub => self.emit(autosynth_isa_aarch64::SubImm { rd, rn, imm }),
            _ => todo!("ALU-imm op {:?} not yet supported", op),
        }
    }

    fn resolve_patches(&mut self) -> Result<(), CodegenError> {
        for &(patch_offset, target) in &self.patches {
            let target_offset = self.labels.get(&target).ok_or(CodegenError::UnresolvedLabel(target))?;
            let disp = *target_offset as i32 - patch_offset as i32;
            let old_word = self.code[patch_offset];
            let cond_bits = old_word & 0xF;
            let imm19 = ((disp as u32) & 0x7FFFF) << 5;
            self.code[patch_offset] = 0x54000000 | imm19 | cond_bits;
        }
        Ok(())
    }
}

fn detect_branches(code: &[u32]) -> Vec<BranchInfo> {
    let mut branches = Vec::new();
    for (i, &word) in code.iter().enumerate() {
        let top8 = word >> 24;
        let (offset_words, conditional) = match top8 {
            0x14..=0x17 => (sign_extend((word & 0x03FF_FFFF) as i32, 26), false),
            0x94..=0x97 => (sign_extend((word & 0x03FF_FFFF) as i32, 26), false),
            0x54 => { let imm19 = ((word >> 5) & 0x7FFFF) as i32; (sign_extend(imm19, 19), (word & 0xF) != 14) }
            0x34 | 0x35 | 0xB4 | 0xB5 => (sign_extend(((word >> 5) & 0x7FFFF) as i32, 19), true),
            _ => continue,
        };
        branches.push(BranchInfo { offset: i * 4, target: ((i as i64 + offset_words as i64) * 4) as usize, is_conditional: conditional });
    }
    branches
}

fn sign_extend(val: i32, bits: u32) -> i32 { let shift = 32 - bits; (val << shift) >> shift }

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
        let fibre = f.define_vstack(VStack { base: fsp, offset: 0 });
        f.entry_block(crate::BlockId::Entry);
        f.push_i64(fibre, Value::Reg(lr));
        let mut cb = CodeBuilder::new();
        f.build(&mut cb);
        let func = &cb.functions()[0];
        let code = backend.lower(func).unwrap();
        assert_eq!(code.len(), 4);
        let word = u32::from_le_bytes([code[0], code[1], code[2], code[3]]);
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
        let scratch = backend.scratch();
        assert!(!scratch.contains(&PhysReg(28)));
        assert!(!scratch.contains(&PhysReg(29)));
        assert!(!scratch.contains(&PhysReg(30)));
    }

    #[test]
    fn use_isa_reg_define64() {
        let mut backend = Aarch64Backend::new();
        backend.use_isa_reg("lbp", IsaReg::FramePointer);
        backend.use_isa_reg("lr", IsaReg::ReturnAddress);
        backend.use_isa_reg("fsp", IsaReg::StackPointer);
        let fuel = backend.use_isa_reg("fuel", IsaReg::Define64(0));
        assert_eq!(fuel, Register::Phys(0));
        let ctx = backend.use_isa_reg("ctx", IsaReg::Define64(-1));
        assert_eq!(ctx, Register::Phys(27));
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
        for (_, phys) in &backend.assignments {
            assert!(!backend.scratch().contains(phys), "assigned reg {phys:?} found in scratch pool");
        }
        let mut seen = std::collections::HashSet::new();
        for reg in backend.scratch() { assert!(seen.insert(reg), "duplicate in scratch pool: {reg:?}"); }
    }
}
