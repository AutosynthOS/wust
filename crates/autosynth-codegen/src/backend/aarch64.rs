use std::collections::HashMap;

use autosynth_isa_aarch64::{
    Aarch64Inst, Aarch64Instruction, BCond, Cond, GprOrSp, GprOrZr, LdrPost, LdrUoff, Movz,
    OrrReg, Ret, SImm9, StrPre, StrUoff, SubsImm, SubsReg, UImm12, UImm16,
    reg::{Gpr, GprId, WGpr, XGpr},
};

use super::BackendEmitter;
use autosynth_isa::PReg;
use crate::CodegenError;
use crate::debugger::Debugger;
use crate::disasm::table::Align;
use crate::disasm::{BlockLabel, BranchInfo, DisasmInst, DisasmMetadata, RegisterRenames};
use crate::ir::block::BlockId;
use crate::ir::function::{FunctionIdx, IRFunction, IsaReg};
use crate::ir::instruction::{AluOp, IrInst, Operand};
use autosynth_ir::CompOp;
use autosynth_isa::Width;
use crate::ir::{Register, VReg, VRegDef, Value};
use crate::regalloc::RegCache;

/// AArch64 backend: manages the ARM64 register pool and lowers IR to native machine code.
pub struct Aarch64Backend {
    pool: Vec<PReg>,
    assignments: HashMap<&'static str, PReg>,
}

impl BackendEmitter for Aarch64Backend {
    fn use_isa_reg(&mut self, name: &'static str, role: IsaReg) -> Register {
        let phys = if let Some(fixed) = Self::fixed_phys(role) {
            self.pool.retain(|r| *r != fixed);
            fixed
        } else {
            let IsaReg::Define64(idx) = role else {
                unreachable!()
            };
            if idx >= 0 {
                self.pool.remove(idx as usize)
            } else {
                let i = self.pool.len().wrapping_add(idx as isize as usize);
                self.pool.remove(i)
            }
        };
        self.assignments.insert(name, phys);
        Register::PReg(phys, Width::W64)
    }

    fn scratch(&self) -> &[PReg] {
        &self.pool
    }

    fn lower(&self, func: &IRFunction) -> Result<Vec<u8>, CodegenError> {
        let (bytes, _) = self.lower_with_disasm(func, None)?;
        Ok(bytes)
    }
}

impl Aarch64Backend {
    /// Create a new AArch64 backend with the full general-purpose register pool.
    pub fn new() -> Self {
        let pool = (0u8..=30).filter(|&r| r != 18).map(PReg).collect();
        Self {
            pool,
            assignments: HashMap::new(),
        }
    }

    /// Look up a named register that was previously reserved.
    pub fn get(&self, name: &str) -> PReg {
        self.assignments[name]
    }

    fn fixed_phys(role: IsaReg) -> Option<PReg> {
        match role {
            IsaReg::FramePointer => Some(PReg(29)),
            IsaReg::StackPointer => Some(PReg(28)),
            IsaReg::ReturnAddress => Some(PReg(30)),
            IsaReg::Define64(_) => None,
        }
    }

    fn phys_to_wgpr(reg: PReg) -> WGpr {
        WGpr(GprId::from_index(reg.0))
    }
    fn phys_to_xgpr(reg: PReg) -> XGpr {
        XGpr(GprId::from_index(reg.0))
    }

    fn reg_to_xgpr(reg: Register) -> Result<XGpr, CodegenError> {
        match reg {
            Register::PReg(p, _) => Ok(XGpr(GprId::from_index(p.0))),
            Register::VReg(v, _) => Err(CodegenError::InvalidRegister(format!(
                "virtual register {v} in lowering (expected physical)"
            ))),
        }
    }

    fn cmp_op_to_cond(op: AluOp) -> Cond {
        match op {
            AluOp::Comp(c) => match c {
                CompOp::Eq => Cond::EQ,
                CompOp::Ne => Cond::NE,
                CompOp::LtS => Cond::LT,
                CompOp::LtU => Cond::CC,
                CompOp::GtS => Cond::GT,
                CompOp::GtU => Cond::HI,
                CompOp::LeS => Cond::LE,
                CompOp::LeU => Cond::LS,
                CompOp::GeS => Cond::GE,
                CompOp::GeU => Cond::CS,
            },
            _ => unreachable!("cmp_op_to_cond called with non-comparison op: {op}"),
        }
    }

    /// Lower an IR function to machine code bytes and structured disassembly metadata.
    ///
    /// When a [`Debugger`] is provided, records block boundaries, IR-to-group
    /// mappings, and per-instruction machine code for visualization.
    pub fn lower_with_disasm(
        &self,
        func: &IRFunction,
        debugger: Option<&mut Debugger>,
    ) -> Result<(Vec<u8>, DisasmMetadata), CodegenError> {
        let mut ctx = LowerCtx::new(&self.pool, &func.vreg_defs, debugger, &self.assignments);
        let mut block_labels: Vec<BlockLabel> = Vec::new();
        let mut ir_index = 0usize;

        for (block_idx, block) in func.blocks.iter().enumerate() {
            let next_block = func.blocks.get(block_idx + 1).map(|b| b.id);

            block_labels.push(BlockLabel {
                offset: ctx.code.len() * 4,
                id: block.id,
                name: None,
            });
            ctx.labels.insert(block.id, ctx.code.len());
            if block.id != BlockId::Entry {
                ctx.cache.invalidate_all();
            }

            for inst in &block.instructions {
                ctx.dbg(|dbg, _| dbg.begin_ir_inst(ir_index));
                ctx.lower_inst(inst, func, next_block)?;
                ir_index += 1;
            }
        }

        ctx.resolve_patches()?;

        let instructions: Vec<DisasmInst> = ctx
            .disasm
            .iter()
            .enumerate()
            .map(|(i, asm)| DisasmInst {
                offset: i * 4,
                text: asm.clone(),
                annotation: None,
            })
            .collect();
        let branches = detect_branches(&ctx.code);
        let meta = DisasmMetadata {
            instructions,
            block_labels,
            branches,
            signature: None,
        };
        Ok((ctx.to_bytes(), meta))
    }
}

struct PendingCmp {
    cond: Cond,
}

struct LowerCtx<'a> {
    code: Vec<u32>,
    cache: RegCache,
    vreg_defs: &'a [VRegDef],
    labels: HashMap<BlockId, usize>,
    patches: Vec<(usize, BlockId)>,
    pending_cmp: Option<PendingCmp>,
    disasm: Vec<String>,
    debugger: Option<&'a mut Debugger>,
    /// Register display names built from backend global assignments.
    renames: RegisterRenames,
}

impl<'a> LowerCtx<'a> {
    fn new(
        scratch: &[PReg],
        vreg_defs: &'a [VRegDef],
        mut debugger: Option<&'a mut Debugger>,
        assignments: &HashMap<&'static str, PReg>,
    ) -> Self {
        if let Some(dbg) = &mut debugger {
            dbg.add_machine_column("addr", Align::Right);
            dbg.add_machine_column("asm", Align::Left);
        }
        let mut renames = RegisterRenames::new();
        for (&name, &phys) in assignments {
            let display = format!("g.{name}");
            renames.add(&format!("x{}", phys.0), &display);
            renames.add(&format!("w{}", phys.0), &display);
        }
        Self {
            code: Vec::with_capacity(64),
            cache: RegCache::new(scratch),
            vreg_defs,
            labels: HashMap::new(),
            patches: Vec::new(),
            pending_cmp: None,
            disasm: Vec::new(),
            debugger,
            renames,
        }
    }

    /// Run a closure with the debugger if one is attached.
    ///
    /// When no debugger is present the closure is never called — no string
    /// formatting, no allocations, zero cost. The closure also receives the
    /// [`RegisterRenames`] so it can format register names without a separate
    /// borrow of `self`.
    fn dbg(&mut self, f: impl FnOnce(&mut Debugger, &RegisterRenames)) {
        if let Some(dbg) = &mut self.debugger {
            f(dbg, &self.renames);
        }
    }

    fn emit(&mut self, inst: Aarch64Instruction) {
        let raw = format!("{inst}");
        let text = self.renames.apply(&raw);
        let offset = self.code.len() * 4;
        self.dbg(|dbg, _| {
            dbg.emit_machine_inst();
            dbg.set_machine("addr", &format!("{offset:04x}"));
            dbg.set_machine("asm", &text);
        });
        self.disasm.push(text);
        self.code.push(inst.encode_word());
    }

    fn resolve_operand(&mut self, op: Operand, func: &IRFunction) -> Result<PReg, CodegenError> {
        match op {
            Operand::PReg(p, _) => Ok(p),
            Operand::VReg(vreg, _) => {
                let result = self.cache.ensure(vreg, self.vreg_defs)?;
                if let Some(evicted) = result.evicted {
                    if evicted.needs_store {
                        self.emit_store(evicted.vreg, evicted.reg, func)?;
                    }
                }
                if result.needs_load {
                    self.emit_load_or_remat(vreg, result.reg, func)?;
                }
                Ok(result.reg)
            }
            Operand::Imm32(_) | Operand::Imm64(_) => Err(CodegenError::InvalidRegister(
                "cannot resolve immediate as a register".into(),
            )),
        }
    }

    fn resolve_dst(&mut self, reg: Register, func: &IRFunction) -> Result<PReg, CodegenError> {
        match reg {
            Register::PReg(p, _) => Ok(p),
            Register::VReg(v, _) => {
                let result = self.cache.define(v, self.vreg_defs)?;
                if let Some(evicted) = result.evicted {
                    if evicted.needs_store {
                        self.emit_store(evicted.vreg, evicted.reg, func)?;
                    }
                }
                Ok(result.reg)
            }
        }
    }

    fn try_imm(&self, op: Operand) -> Option<i64> {
        match op {
            Operand::Imm32(n) => Some(n as i64),
            Operand::Imm64(n) => Some(n),
            Operand::VReg(vreg, _) => match self.vreg_defs[vreg.0 as usize].value {
                Value::ConstI32(n) => Some(n as i64),
                Value::ConstI64(n) => Some(n),
                _ => None,
            },
            Operand::PReg(_, _) => None,
        }
    }

    fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(self.code.len() * 4);
        for &word in &self.code {
            bytes.extend_from_slice(&word.to_le_bytes());
        }
        bytes
    }

    /// Dispatch an IR instruction to the appropriate lowering helper.
    ///
    /// `next_block` is the block that follows in layout order — used for
    /// fallthrough elimination (unconditional branches to the next block
    /// emit no code).
    fn lower_inst(
        &mut self,
        inst: &IrInst,
        func: &IRFunction,
        next_block: Option<BlockId>,
    ) -> Result<(), CodegenError> {
        match inst {
            IrInst::Alu { op, dst, lhs, rhs } => self.lower_alu(*op, *dst, *lhs, *rhs, func),
            IrInst::BrIf {
                block_else, ..
            } => self.lower_br_if(*block_else),
            IrInst::Branch { target } if Some(*target) == next_block => Ok(()),
            IrInst::Branch { target } => self.lower_branch(*target),
            IrInst::Call {
                func_idx,
                args,
                results,
                frame_advance,
            } => self.lower_call(func_idx, args, results, *frame_advance, func),
            IrInst::Load { dst, .. } => {
                let vreg = match dst {
                    Register::VReg(v, _) => *v,
                    Register::PReg(_, _) => {
                        return Err(CodegenError::InvalidRegister(
                            "Load dst must be a VReg".into(),
                        ))
                    }
                };
                let def = &self.vreg_defs[vreg.0 as usize];
                self.lower_stack_pop(def, func)
            }
            IrInst::Store { src, .. } => {
                let vreg = match src {
                    Operand::VReg(v, _) => *v,
                    _ => {
                        return Err(CodegenError::InvalidRegister(
                            "Store src must be a VReg".into(),
                        ))
                    }
                };
                let def = &self.vreg_defs[vreg.0 as usize];
                self.lower_stack_push(def, func)
            }
            IrInst::Return => self.lower_return(&[], false, func),
            IrInst::Move { .. } => todo!("Move not implemented in old backend"),
            IrInst::Skipped(_) => Ok(()),
        }
    }

    fn lower_stack_push(&mut self, def: &VRegDef, func: &IRFunction) -> Result<(), CodegenError> {
        match def.value {
            Value::Destination => {}
            Value::ConstI64(0) => {}
            Value::ConstI32(n) => {
                let result = self.cache.define(def.id, self.vreg_defs)?;
                if let Some(evicted) = result.evicted {
                    if evicted.needs_store {
                        self.emit_store(evicted.vreg, evicted.reg, func)?;
                    }
                }
                self.emit_i32_const(result.reg, n);
            }
            Value::ConstI64(n) => {
                let result = self.cache.define(def.id, self.vreg_defs)?;
                if let Some(evicted) = result.evicted {
                    if evicted.needs_store {
                        self.emit_store(evicted.vreg, evicted.reg, func)?;
                    }
                }
                self.emit_i64_const(result.reg, n);
            }
            Value::VReg(src) => {
                let src_result = self.cache.ensure(src, self.vreg_defs)?;
                if let Some(evicted) = src_result.evicted {
                    if evicted.needs_store {
                        self.emit_store(evicted.vreg, evicted.reg, func)?;
                    }
                }
                if src_result.needs_load {
                    self.emit_load_or_remat(src, src_result.reg, func)?;
                }
                self.cache
                    .alias(def.id, src)
                    .expect("alias failed after ensure");
            }
            Value::Reg(reg) => {
                let slot = def.slot.expect("StackPush(Reg) on temp vreg");
                let base_reg = func.vstacks[slot.vstack.0 as usize].base;
                let base = Aarch64Backend::reg_to_xgpr(base_reg)?;
                let offset = -(slot.size as i32);
                let imm = SImm9::try_from(offset).map_err(|_| CodegenError::OffsetOutOfRange {
                    offset: offset as u32,
                    max: 255,
                })?;
                self.emit(Aarch64Instruction::StrPre(StrPre {
                    rt: GprOrZr::from(Aarch64Backend::reg_to_xgpr(reg)?),
                    rn: GprOrSp::from(Gpr::X(base)),
                    imm,
                }));
            }
            Value::Param(i) => {
                let cc_reg = PReg(9 + i as u8);
                self.cache.bind(def.id, cc_reg);
            }
        }
        Ok(())
    }

    fn lower_stack_pop(&mut self, def: &VRegDef, func: &IRFunction) -> Result<(), CodegenError> {
        if let Value::Reg(reg) = def.value {
            let slot = def.slot.expect("StackPop(Reg) on temp vreg");
            let base_reg = func.vstacks[slot.vstack.0 as usize].base;
            let base = Aarch64Backend::reg_to_xgpr(base_reg)?;
            let imm = SImm9::try_from(slot.size as i32).map_err(|_| CodegenError::OffsetOutOfRange {
                offset: slot.size as u32,
                max: 255,
            })?;
            self.emit(Aarch64Instruction::LdrPost(LdrPost {
                rt: GprOrZr::from(Aarch64Backend::reg_to_xgpr(reg)?),
                rn: GprOrSp::from(Gpr::X(base)),
                imm,
            }));
            return Ok(());
        }
        if self.cache.lookup(def.id).is_some() {
            let result = self.cache.ensure(def.id, self.vreg_defs)?;
            if result.needs_load {
                self.emit_load_or_remat(def.id, result.reg, func)?;
            }
        }
        Ok(())
    }

    fn lower_alu(
        &mut self,
        op: AluOp,
        dst: Register,
        lhs: Operand,
        rhs: Operand,
        func: &IRFunction,
    ) -> Result<(), CodegenError> {
        let is_32 = matches!(lhs.width(), Width::W32);

        if let AluOp::Comp(_) = op {
            return self.lower_cmp(op, dst, lhs, rhs, is_32, func);
        }

        let lhs_phys = self.resolve_operand(lhs, func)?;
        let dst_phys = self.resolve_dst(dst, func)?;

        if let Some(imm) = self.try_imm(rhs) {
            if let Ok(imm12) = UImm12::try_from(imm) {
                self.emit_alu_imm(op, dst_phys, lhs_phys, imm12, is_32);
                if let Operand::VReg(v, _) = rhs {
                    self.cache.release(v);
                }
                return Ok(());
            }
        }
        let rhs_phys = self.resolve_operand(rhs, func)?;
        self.emit_alu_reg(op, dst_phys, lhs_phys, rhs_phys, is_32);
        Ok(())
    }

    fn lower_cmp(
        &mut self,
        op: AluOp,
        dst: Register,
        lhs: Operand,
        rhs: Operand,
        is_32: bool,
        func: &IRFunction,
    ) -> Result<(), CodegenError> {
        let lhs_phys = self.resolve_operand(lhs, func)?;

        let rd = match dst {
            Register::PReg(p, _) => {
                if is_32 {
                    GprOrZr::from(Aarch64Backend::phys_to_wgpr(p))
                } else {
                    GprOrZr::from(Aarch64Backend::phys_to_xgpr(p))
                }
            }
            Register::VReg(_, _) => {
                if is_32 {
                    GprOrZr::Wzr
                } else {
                    GprOrZr::Xzr
                }
            }
        };

        if let Some(imm) = self.try_imm(rhs) {
            if let Ok(imm12) = UImm12::try_from(imm) {
                let rn = if is_32 {
                    GprOrSp::from(Aarch64Backend::phys_to_wgpr(lhs_phys))
                } else {
                    GprOrSp::from(Gpr::X(Aarch64Backend::phys_to_xgpr(lhs_phys)))
                };
                self.emit(Aarch64Instruction::SubsImm(SubsImm { rd, rn, imm: imm12 }));
                if let Operand::VReg(v, _) = rhs {
                    self.cache.release(v);
                }
                self.pending_cmp = Some(PendingCmp {
                    cond: Aarch64Backend::cmp_op_to_cond(op),
                });
                return Ok(());
            }
        }

        let rhs_phys = self.resolve_operand(rhs, func)?;
        let rn = if is_32 {
            GprOrZr::from(Aarch64Backend::phys_to_wgpr(lhs_phys))
        } else {
            GprOrZr::from(Aarch64Backend::phys_to_xgpr(lhs_phys))
        };
        let rm = if is_32 {
            GprOrZr::from(Aarch64Backend::phys_to_wgpr(rhs_phys))
        } else {
            GprOrZr::from(Aarch64Backend::phys_to_xgpr(rhs_phys))
        };
        self.emit(Aarch64Instruction::SubsReg(SubsReg { rd, rn, rm }));
        self.pending_cmp = Some(PendingCmp {
            cond: Aarch64Backend::cmp_op_to_cond(op),
        });
        Ok(())
    }

    fn lower_br_if(&mut self, block_else: BlockId) -> Result<(), CodegenError> {
        let pending = self.pending_cmp.take().expect("BrIf without preceding Cmp");
        let else_offset = self.code.len();
        self.emit(Aarch64Instruction::BCond(BCond {
            cond: pending.cond.invert(),
            offset: 0,
        }));
        self.patches.push((else_offset, block_else));
        Ok(())
    }

    fn lower_branch(&mut self, target: BlockId) -> Result<(), CodegenError> {
        let offset = self.code.len();
        self.emit(Aarch64Instruction::BCond(BCond {
            cond: Cond::AL,
            offset: 0,
        }));
        self.patches.push((offset, target));
        Ok(())
    }

    fn lower_call(
        &mut self,
        func_idx: &FunctionIdx,
        args: &[VReg],
        results: &[VReg],
        frame_advance: u32,
        func: &IRFunction,
    ) -> Result<(), CodegenError> {
        let dirty = self.cache.flush_dirty();
        for (phys, vreg) in dirty {
            self.emit_store(vreg, phys, func)?;
        }

        for (i, &arg) in args.iter().enumerate() {
            let r = self.cache.ensure(arg, self.vreg_defs)?;
            if let Some(evicted) = r.evicted {
                if evicted.needs_store {
                    self.emit_store(evicted.vreg, evicted.reg, func)?;
                }
            }
            if r.needs_load {
                self.emit_load_or_remat(arg, r.reg, func)?;
            }
            let cc_reg = PReg(9 + i as u8);
            if r.reg != cc_reg {
                let is_32 = matches!(self.vreg_defs[arg.0 as usize].width, Width::W32);
                self.emit_mov(cc_reg, r.reg, is_32);
            }
        }

        if frame_advance > 0 {
            let imm =
                UImm12::try_from(frame_advance).map_err(|_| CodegenError::OffsetOutOfRange {
                    offset: frame_advance,
                    max: 4095,
                })?;
            let fp = GprOrSp::from(Gpr::X(XGpr(GprId::R29)));
            self.emit(Aarch64Instruction::AddImm(autosynth_isa_aarch64::AddImm {
                rd: fp,
                rn: fp,
                imm,
            }));
        }

        let mut param_offset = 0u32;
        for (i, &arg) in args.iter().enumerate() {
            let cc_reg = PReg(9 + i as u8);
            match self.vreg_defs[arg.0 as usize].width {
                Width::W32 => {
                    let uimm = UImm12::try_from(param_offset / 4).map_err(|_| {
                        CodegenError::OffsetOutOfRange {
                            offset: param_offset,
                            max: 4095 * 4,
                        }
                    })?;
                    self.emit(Aarch64Instruction::StrUoff(StrUoff {
                        rt: GprOrZr::from(Aarch64Backend::phys_to_wgpr(cc_reg)),
                        rn: GprOrSp::from(Gpr::X(XGpr(GprId::R29))),
                        offset: uimm,
                    }));
                    param_offset += 4;
                }
                Width::W64 => {
                    let uimm = UImm12::try_from(param_offset / 8).map_err(|_| {
                        CodegenError::OffsetOutOfRange {
                            offset: param_offset,
                            max: 4095 * 8,
                        }
                    })?;
                    self.emit(Aarch64Instruction::StrUoff(StrUoff {
                        rt: GprOrZr::from(Aarch64Backend::phys_to_xgpr(cc_reg)),
                        rn: GprOrSp::from(Gpr::X(XGpr(GprId::R29))),
                        offset: uimm,
                    }));
                    param_offset += 8;
                }
            }
        }

        let FunctionIdx::User(_idx) = func_idx;
        let entry_offset = self.labels.get(&BlockId::Entry).copied().unwrap_or(0);
        let disp = entry_offset as i32 - self.code.len() as i32;
        self.emit(Aarch64Instruction::Bl(autosynth_isa_aarch64::Bl {
            offset: disp,
        }));

        if frame_advance > 0 {
            let imm =
                UImm12::try_from(frame_advance).map_err(|_| CodegenError::OffsetOutOfRange {
                    offset: frame_advance,
                    max: 4095,
                })?;
            let fp = GprOrSp::from(Gpr::X(XGpr(GprId::R29)));
            self.emit(Aarch64Instruction::SubImm(autosynth_isa_aarch64::SubImm {
                rd: fp,
                rn: fp,
                imm,
            }));
        }

        self.cache.invalidate_all();

        for (i, &res) in results.iter().enumerate() {
            let cc_reg = PReg(9 + i as u8);
            self.cache.bind_dirty(res, cc_reg);
            self.emit_store(res, cc_reg, func)?;
        }
        Ok(())
    }

    fn lower_return(
        &mut self,
        values: &[VReg],
        flush: bool,
        func: &IRFunction,
    ) -> Result<(), CodegenError> {
        if flush {
            let dirty = self.cache.flush_dirty();
            for (phys, vreg) in dirty {
                self.emit_store(vreg, phys, func)?;
            }
        }
        for (i, &vreg) in values.iter().enumerate() {
            let result = self.cache.ensure(vreg, self.vreg_defs)?;
            if let Some(evicted) = result.evicted {
                if evicted.needs_store {
                    self.emit_store(evicted.vreg, evicted.reg, func)?;
                }
            }
            if result.needs_load {
                self.emit_load_or_remat(vreg, result.reg, func)?;
            }
            let ret_reg = PReg(9 + i as u8);
            if result.reg != ret_reg {
                let is_32 = matches!(self.vreg_defs[vreg.0 as usize].width, Width::W32);
                self.emit_mov(ret_reg, result.reg, is_32);
            }
        }
        self.emit(Aarch64Instruction::Ret(Ret {
            rn: XGpr(GprId::R30),
        }));
        Ok(())
    }

    fn emit_mov(&mut self, dst: PReg, src: PReg, is_32: bool) {
        if is_32 {
            self.emit(Aarch64Instruction::OrrReg(OrrReg {
                rd: GprOrZr::from(Aarch64Backend::phys_to_wgpr(dst)),
                rn: GprOrZr::Wzr,
                rm: GprOrZr::from(Aarch64Backend::phys_to_wgpr(src)),
            }));
        } else {
            self.emit(Aarch64Instruction::OrrReg(OrrReg {
                rd: GprOrZr::from(Aarch64Backend::phys_to_xgpr(dst)),
                rn: GprOrZr::Xzr,
                rm: GprOrZr::from(Aarch64Backend::phys_to_xgpr(src)),
            }));
        }
    }

    /// Load or rematerialize a VReg into a physical register.
    ///
    /// If the VReg is rematerializable (constant), emits `movz` instead
    /// of loading from memory — 1 cycle, no cache pressure.
    fn emit_load_or_remat(
        &mut self,
        vreg: VReg,
        dst: PReg,
        func: &IRFunction,
    ) -> Result<(), CodegenError> {
        let def = &self.vreg_defs[vreg.0 as usize];
        if def.remat {
            return self.emit_remat(def, dst);
        }
        self.emit_load(vreg, dst, func)
    }

    /// Emit a `movz` to rematerialize a constant value.
    fn emit_remat(&mut self, def: &VRegDef, dst: PReg) -> Result<(), CodegenError> {
        match def.value {
            Value::ConstI32(n) => self.emit_i32_const(dst, n),
            Value::ConstI64(n) => self.emit_i64_const(dst, n),
            _ => unreachable!("emit_remat on non-constant value"),
        }
        Ok(())
    }

    /// Emit instructions to materialize an i32 constant into a register.
    ///
    /// Uses `movz` for values 0–65535. Larger values use `movz` + `movk`
    /// to build the full 32-bit value in two halfwords.
    fn emit_i32_const(&mut self, dst: PReg, n: i32) {
        let val = n as u32;
        let lo = (val & 0xFFFF) as u16;
        let hi = (val >> 16) as u16;
        let rd = GprOrZr::from(Aarch64Backend::phys_to_wgpr(dst));
        self.emit(Aarch64Instruction::Movz(Movz {
            rd,
            imm: UImm16::try_from(lo).unwrap(),
            hw: 0,
        }));
        if hi != 0 {
            self.emit(Aarch64Instruction::Movk(autosynth_isa_aarch64::Movk {
                rd,
                imm: UImm16::try_from(hi).unwrap(),
                hw: 1,
            }));
        }
    }

    /// Emit instructions to materialize an i64 constant into a register.
    ///
    /// Uses `movz` for the lowest non-zero halfword, then `movk` for each
    /// additional non-zero halfword. Up to 4 instructions for a full 64-bit value.
    fn emit_i64_const(&mut self, dst: PReg, n: i64) {
        let val = n as u64;
        let rd = GprOrZr::from(Aarch64Backend::phys_to_xgpr(dst));
        let halfwords: [u16; 4] = [
            (val & 0xFFFF) as u16,
            ((val >> 16) & 0xFFFF) as u16,
            ((val >> 32) & 0xFFFF) as u16,
            ((val >> 48) & 0xFFFF) as u16,
        ];
        // Find the first non-zero halfword (or hw0 if all zero).
        let first_nz = halfwords.iter().position(|&h| h != 0).unwrap_or(0);
        self.emit(Aarch64Instruction::Movz(Movz {
            rd,
            imm: UImm16::try_from(halfwords[first_nz]).unwrap(),
            hw: first_nz as u8,
        }));
        for (i, &hw) in halfwords.iter().enumerate() {
            if i != first_nz && hw != 0 {
                self.emit(Aarch64Instruction::Movk(autosynth_isa_aarch64::Movk {
                    rd,
                    imm: UImm16::try_from(hw).unwrap(),
                    hw: i as u8,
                }));
            }
        }
    }

    fn emit_load(
        &mut self,
        vreg: VReg,
        dst: PReg,
        func: &IRFunction,
    ) -> Result<(), CodegenError> {
        let def = &self.vreg_defs[vreg.0 as usize];
        let slot = def
            .slot
            .expect("emit_load on temp vreg (no canonical slot)");
        let vstack = &func.vstacks[slot.vstack.0 as usize];
        let base = Aarch64Backend::reg_to_xgpr(vstack.base)?;
        let offset = slot.byte_offset;
        match def.width {
            Width::W32 => {
                let uimm =
                    UImm12::try_from(offset / 4).map_err(|_| CodegenError::OffsetOutOfRange {
                        offset: offset as u32,
                        max: 4095 * 4,
                    })?;
                self.emit(Aarch64Instruction::LdrUoff(LdrUoff {
                    rt: GprOrZr::from(Aarch64Backend::phys_to_wgpr(dst)),
                    rn: GprOrSp::from(Gpr::X(base)),
                    offset: uimm,
                }));
            }
            Width::W64 => {
                let uimm =
                    UImm12::try_from(offset / 8).map_err(|_| CodegenError::OffsetOutOfRange {
                        offset: offset as u32,
                        max: 4095 * 8,
                    })?;
                self.emit(Aarch64Instruction::LdrUoff(LdrUoff {
                    rt: GprOrZr::from(Aarch64Backend::phys_to_xgpr(dst)),
                    rn: GprOrSp::from(Gpr::X(base)),
                    offset: uimm,
                }));
            }
        }
        Ok(())
    }

    fn emit_store(
        &mut self,
        vreg: VReg,
        src: PReg,
        func: &IRFunction,
    ) -> Result<(), CodegenError> {
        let def = &self.vreg_defs[vreg.0 as usize];
        let slot = def
            .slot
            .expect("emit_store on temp vreg (no canonical slot)");
        let vstack = &func.vstacks[slot.vstack.0 as usize];
        let base = Aarch64Backend::reg_to_xgpr(vstack.base)?;
        let offset = slot.byte_offset;
        match def.width {
            Width::W32 => {
                let uimm =
                    UImm12::try_from(offset / 4).map_err(|_| CodegenError::OffsetOutOfRange {
                        offset: offset as u32,
                        max: 4095 * 4,
                    })?;
                self.emit(Aarch64Instruction::StrUoff(StrUoff {
                    rt: GprOrZr::from(Aarch64Backend::phys_to_wgpr(src)),
                    rn: GprOrSp::from(Gpr::X(base)),
                    offset: uimm,
                }));
            }
            Width::W64 => {
                let uimm =
                    UImm12::try_from(offset / 8).map_err(|_| CodegenError::OffsetOutOfRange {
                        offset: offset as u32,
                        max: 4095 * 8,
                    })?;
                self.emit(Aarch64Instruction::StrUoff(StrUoff {
                    rt: GprOrZr::from(Aarch64Backend::phys_to_xgpr(src)),
                    rn: GprOrSp::from(Gpr::X(base)),
                    offset: uimm,
                }));
            }
        }
        Ok(())
    }

    fn emit_alu_reg(&mut self, op: AluOp, dst: PReg, lhs: PReg, rhs: PReg, is_32: bool) {
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
            AluOp::Add => self.emit(Aarch64Instruction::AddReg(autosynth_isa_aarch64::AddReg {
                rd,
                rn,
                rm,
            })),
            AluOp::Sub => self.emit(Aarch64Instruction::SubReg(autosynth_isa_aarch64::SubReg {
                rd,
                rn,
                rm,
            })),
            _ => todo!("ALU op {:?} not yet lowered", op),
        }
    }

    fn emit_alu_imm(&mut self, op: AluOp, dst: PReg, src: PReg, imm: UImm12, is_32: bool) {
        let (rd, rn) = if is_32 {
            (
                GprOrSp::from(Aarch64Backend::phys_to_wgpr(dst)),
                GprOrSp::from(Aarch64Backend::phys_to_wgpr(src)),
            )
        } else {
            (
                GprOrSp::from(Gpr::X(Aarch64Backend::phys_to_xgpr(dst))),
                GprOrSp::from(Gpr::X(Aarch64Backend::phys_to_xgpr(src))),
            )
        };
        match op {
            AluOp::Add => self.emit(Aarch64Instruction::AddImm(autosynth_isa_aarch64::AddImm {
                rd,
                rn,
                imm,
            })),
            AluOp::Sub => self.emit(Aarch64Instruction::SubImm(autosynth_isa_aarch64::SubImm {
                rd,
                rn,
                imm,
            })),
            _ => todo!("ALU-imm op {:?} not yet supported", op),
        }
    }

    fn resolve_patches(&mut self) -> Result<(), CodegenError> {
        for &(patch_offset, target) in &self.patches {
            let target_offset = self
                .labels
                .get(&target)
                .ok_or(CodegenError::UnresolvedLabel(target))?;
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
            0x54 => {
                let imm19 = ((word >> 5) & 0x7FFFF) as i32;
                (sign_extend(imm19, 19), (word & 0xF) != 14)
            }
            0x34 | 0x35 | 0xB4 | 0xB5 => (sign_extend(((word >> 5) & 0x7FFFF) as i32, 19), true),
            _ => continue,
        };
        branches.push(BranchInfo {
            offset: i * 4,
            target: ((i as i64 + offset_words as i64) * 4) as usize,
            is_conditional: conditional,
        });
    }
    branches
}

fn sign_extend(val: i32, bits: u32) -> i32 {
    let shift = 32 - bits;
    (val << shift) >> shift
}
