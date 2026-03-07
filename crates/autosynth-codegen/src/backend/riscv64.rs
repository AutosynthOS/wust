use std::collections::HashMap;

use autosynth_isa_riscv64::{
    Add, Addi, Addiw, Addw, Beq, Bge, Bgeu, Blt, Bltu, Bne, Jal, Jalr, Ld, Lui, Lw, Or, Sd, Sub,
    Subw, Sw,
    Rv64Inst, SImm12, SImm20, BImm13, JImm21,
    reg::{Gpr, GprId},
};

use super::{BackendEmitter, PhysReg};
use crate::CodegenError;
use crate::disasm::{BlockLabel, BranchInfo, DisasmInst, DisasmMetadata};
use crate::ir::block::BlockId;
use crate::ir::function::{FunctionIdx, IRFunction, IsaReg};
use crate::ir::instruction::{AluOp, CmpOp, IrInst};
use crate::ir::{IrType, Register, VReg, VRegDef, Value};
use crate::regalloc::RegCache;

/// RISC-V 64-bit backend: manages the RV64I register pool and lowers IR
/// to native machine code.
///
/// The caller reserves named registers via [`BackendEmitter::use_isa_reg`]
/// before building the IR. The remaining pool is used as scratch registers
/// by the register cache during lowering.
///
/// Key architectural difference from AArch64: RISC-V has no condition flags.
/// Comparisons and conditional branches are fused — the branch instruction
/// itself compares two registers directly (e.g. `blt rs1, rs2, offset`).
pub struct Riscv64Backend {
    pool: Vec<PhysReg>,
    assignments: HashMap<&'static str, PhysReg>,
}

impl Riscv64Backend {
    /// Create a new RV64I backend with the full general-purpose register pool.
    ///
    /// Excludes x0 (hardwired zero), x3 (gp), and x4 (tp) — these are
    /// not allocatable for general use.
    pub fn new() -> Self {
        let pool = (1u8..=31)
            .filter(|&r| r != 3 && r != 4)
            .map(PhysReg)
            .collect();
        Self {
            pool,
            assignments: HashMap::new(),
        }
    }

    /// Look up a named register that was previously reserved via
    /// [`use_isa_reg`](BackendEmitter::use_isa_reg).
    ///
    /// # Panics
    ///
    /// Panics if `name` was never registered.
    pub fn get(&self, name: &str) -> PhysReg {
        self.assignments[name]
    }

    /// Map a fixed ISA role to its RISC-V physical register.
    fn fixed_phys(role: IsaReg) -> Option<PhysReg> {
        match role {
            IsaReg::FramePointer => Some(PhysReg(8)),   // s0/fp
            IsaReg::StackPointer => Some(PhysReg(19)),   // s3 (software SP)
            IsaReg::ReturnAddress => Some(PhysReg(1)),   // ra
            IsaReg::Define64(_) => None,
        }
    }

    /// Convert a PhysReg to a RISC-V Gpr.
    fn phys_to_gpr(reg: PhysReg) -> Gpr {
        Gpr(GprId::from_index(reg.0))
    }
}

impl BackendEmitter for Riscv64Backend {
    fn use_isa_reg(&mut self, name: &'static str, role: IsaReg) -> Register {
        let phys = if let Some(fixed) = Self::fixed_phys(role) {
            self.pool.retain(|r| *r != fixed);
            fixed
        } else {
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

    fn lower(&self, func: &IRFunction) -> Result<Vec<u8>, CodegenError> {
        let (bytes, _) = self.lower_with_disasm(func)?;
        Ok(bytes)
    }
}

impl Riscv64Backend {
    /// Lower an IR function to machine code bytes and a human-readable
    /// disassembly listing.
    pub fn lower_with_disasm(
        &self,
        func: &IRFunction,
    ) -> Result<(Vec<u8>, DisasmMetadata), CodegenError> {
        let mut ctx = LowerCtx::new(&self.pool, &func.vreg_defs);
        let mut block_labels: Vec<BlockLabel> = Vec::new();

        for block in &func.blocks {
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
                ctx.lower_inst(inst, func)?;
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

/// Deferred comparison waiting for a BrIf to fuse into a conditional branch.
///
/// Unlike AArch64, RISC-V has no condition flags. The branch instruction
/// itself compares two registers. We store the comparison operands and
/// operation so that BrIf can emit the appropriate branch instruction.
struct PendingCmp {
    op: CmpOp,
    lhs: PhysReg,
    rhs: PhysReg,
}

/// Lowering context — mutable state for a single function's code generation.
struct LowerCtx<'a> {
    code: Vec<u32>,
    cache: RegCache,
    vreg_defs: &'a [VRegDef],
    labels: HashMap<BlockId, usize>,
    /// (code_offset, target_block) — patches for forward branches.
    patches: Vec<(usize, BlockId)>,
    /// Fused compare-and-branch state.
    pending_cmp: Option<PendingCmp>,
    /// Per-word disassembly annotations.
    disasm: Vec<String>,
}

impl<'a> LowerCtx<'a> {
    fn new(scratch: &[PhysReg], vreg_defs: &'a [VRegDef]) -> Self {
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
    fn emit<I: Rv64Inst + core::fmt::Display>(&mut self, inst: I) {
        self.disasm.push(format!("{inst}"));
        self.code.push(inst.encode_word());
    }

    /// Resolve a Register to a PhysReg, emitting a load if needed.
    fn resolve(&mut self, reg: Register, func: &IRFunction) -> Result<PhysReg, CodegenError> {
        match reg {
            Register::Phys(n) => Ok(PhysReg(n)),
            Register::Virtual(id) => {
                let vreg = VReg(id);
                let result = self.cache.ensure(vreg)?;
                if result.needs_load {
                    self.emit_load(vreg, result.reg, func)?;
                }
                Ok(result.reg)
            }
        }
    }

    /// Define a Register in the regcache, returning the PhysReg.
    fn resolve_dst(&mut self, reg: Register) -> Result<PhysReg, CodegenError> {
        match reg {
            Register::Phys(n) => Ok(PhysReg(n)),
            Register::Virtual(id) => self.cache.define(VReg(id)),
        }
    }

    /// Get the IR type for a Register.
    fn reg_type(&self, reg: Register) -> IrType {
        match reg {
            Register::Phys(_) => IrType::I64,
            Register::Virtual(id) => self.vreg_defs[id as usize].ty,
        }
    }

    /// Try to extract a constant value from a Register.
    fn try_const(&self, reg: Register) -> Option<i64> {
        match reg {
            Register::Phys(_) => None,
            Register::Virtual(id) => {
                let def = &self.vreg_defs[id as usize];
                match def.value {
                    Value::ConstI32(n) => Some(n as i64),
                    Value::Const(n) => Some(n),
                    _ => None,
                }
            }
        }
    }

    fn lower_inst(&mut self, inst: &IrInst, func: &IRFunction) -> Result<(), CodegenError> {
        match inst {
            IrInst::StackPush { def } => {
                match def.value {
                    Value::Const(0) => {
                        // Placeholder for ALU/Cmp destination — skip.
                    }
                    Value::ConstI32(n) => {
                        let phys = self.cache.define(def.id)?;
                        let gpr = Riscv64Backend::phys_to_gpr(phys);
                        self.emit_load_imm(gpr, n as i64);
                    }
                    Value::Const(n) => {
                        let phys = self.cache.define(def.id)?;
                        let gpr = Riscv64Backend::phys_to_gpr(phys);
                        self.emit_load_imm(gpr, n);
                    }
                    Value::VReg(src) => {
                        let src_result = self.cache.ensure(src)?;
                        if src_result.needs_load {
                            self.emit_load(src, src_result.reg, func)?;
                        }
                        self.cache.alias(def.id, src)
                            .expect("alias failed after ensure");
                    }
                    Value::Reg(reg) => {
                        // Physical register push (e.g., fibre stack push of ra).
                        let base_reg = func.vstacks[def.slot.vstack.0 as usize].base;
                        let base = Riscv64Backend::phys_to_gpr(self.resolve_phys(base_reg)?);
                        let src = Riscv64Backend::phys_to_gpr(self.resolve_phys(reg)?);
                        let offset = -(def.slot.size as i16);
                        // Pre-decrement: first adjust base, then store.
                        let imm = SImm12::new(offset).map_err(|_| {
                            CodegenError::OffsetOutOfRange {
                                offset: offset as u32,
                                max: 2047,
                            }
                        })?;
                        // addi base, base, -size
                        self.emit(Addi { rd: base, rs1: base, imm });
                        // sd src, 0(base)
                        let zero_imm = SImm12::new(0).unwrap();
                        if def.slot.size == 4 {
                            self.emit(Sw { rs2: src, rs1: base, imm: zero_imm });
                        } else {
                            self.emit(Sd { rs2: src, rs1: base, imm: zero_imm });
                        }
                    }
                    Value::Param(i) => {
                        // Parameters arrive in calling convention registers.
                        // Param 0 in x9, param 1 in x10, etc.
                        let cc_reg = PhysReg(9 + i as u8);
                        self.cache.bind(def.id, cc_reg);
                    }
                }
            }

            IrInst::StackPop { def } => {
                if let Value::Reg(reg) = def.value {
                    // Pop a physical register from the fibre stack (post-increment).
                    let base_reg = func.vstacks[def.slot.vstack.0 as usize].base;
                    let base = Riscv64Backend::phys_to_gpr(self.resolve_phys(base_reg)?);
                    let dst = Riscv64Backend::phys_to_gpr(self.resolve_phys(reg)?);
                    let zero_imm = SImm12::new(0).unwrap();
                    // ld dst, 0(base)
                    if def.slot.size == 4 {
                        self.emit(Lw { rd: dst, rs1: base, imm: zero_imm });
                    } else {
                        self.emit(Ld { rd: dst, rs1: base, imm: zero_imm });
                    }
                    // addi base, base, size
                    let imm = SImm12::new(def.slot.size as i16).map_err(|_| {
                        CodegenError::OffsetOutOfRange {
                            offset: def.slot.size as u32,
                            max: 2047,
                        }
                    })?;
                    self.emit(Addi { rd: base, rs1: base, imm });
                    return Ok(());
                }

                if self.cache.lookup(def.id).is_some() {
                    let result = self.cache.ensure(def.id)?;
                    if result.needs_load {
                        self.emit_load(def.id, result.reg, func)?;
                    }
                }
            }

            IrInst::Alu { op, dst, lhs, rhs } => {
                let lhs_phys = self.resolve(*lhs, func)?;
                let dst_phys = self.resolve_dst(*dst)?;
                let is_32 = matches!(self.reg_type(*lhs), IrType::I32 | IrType::F32);

                // Try to fold rhs into an immediate for add/sub.
                if let Some(imm) = self.try_const(*rhs) {
                    if matches!(op, AluOp::Add | AluOp::Sub) {
                        let eff_imm = if *op == AluOp::Sub { -imm } else { imm };
                        if let Ok(simm) = SImm12::new(eff_imm as i16) {
                            if is_32 {
                                self.emit(Addiw {
                                    rd: Riscv64Backend::phys_to_gpr(dst_phys),
                                    rs1: Riscv64Backend::phys_to_gpr(lhs_phys),
                                    imm: simm,
                                });
                            } else {
                                self.emit(Addi {
                                    rd: Riscv64Backend::phys_to_gpr(dst_phys),
                                    rs1: Riscv64Backend::phys_to_gpr(lhs_phys),
                                    imm: simm,
                                });
                            }
                            if let Register::Virtual(id) = rhs {
                                self.cache.release(VReg(*id));
                            }
                            return Ok(());
                        }
                    }
                }

                let rhs_phys = self.resolve(*rhs, func)?;
                self.emit_alu(*op, dst_phys, lhs_phys, rhs_phys, is_32);
            }

            IrInst::Cmp { op, dst: _, lhs, rhs } => {
                // RISC-V has no flags. Store the operands and operation
                // so BrIf can emit the fused compare-and-branch.
                let lhs_phys = self.resolve(*lhs, func)?;
                let rhs_phys = self.resolve(*rhs, func)?;

                self.pending_cmp = Some(PendingCmp {
                    op: *op,
                    lhs: lhs_phys,
                    rhs: rhs_phys,
                });
            }

            IrInst::BrIf { cond: _, block_if: _, block_else } => {
                let pending = self.pending_cmp.take()
                    .expect("BrIf without preceding Cmp");

                // Emit the *inverted* branch to the else block.
                // The if-true block is the fallthrough.
                let else_offset = self.code.len();
                let placeholder = BImm13::new(0).unwrap();
                let lhs = Riscv64Backend::phys_to_gpr(pending.lhs);
                let rhs = Riscv64Backend::phys_to_gpr(pending.rhs);

                // Invert the condition and emit the appropriate branch.
                // For conditions without a direct branch (GtS, LeS, GtU, LeU),
                // we swap operands to use the available branch instructions.
                match pending.op {
                    // Eq -> branch to else if NOT equal
                    CmpOp::Eq => self.emit(Bne { rs1: lhs, rs2: rhs, imm: placeholder }),
                    // Ne -> branch to else if equal
                    CmpOp::Ne => self.emit(Beq { rs1: lhs, rs2: rhs, imm: placeholder }),
                    // LtS -> branch to else if >= (signed)
                    CmpOp::LtS => self.emit(Bge { rs1: lhs, rs2: rhs, imm: placeholder }),
                    // GeS -> branch to else if < (signed)
                    CmpOp::GeS => self.emit(Blt { rs1: lhs, rs2: rhs, imm: placeholder }),
                    // GtS -> branch to else if <= (signed)
                    // lhs > rhs inverted is lhs <= rhs, i.e. rhs >= lhs
                    CmpOp::GtS => self.emit(Bge { rs1: rhs, rs2: lhs, imm: placeholder }),
                    // LeS -> branch to else if > (signed)
                    // lhs <= rhs inverted is lhs > rhs, i.e. rhs < lhs
                    CmpOp::LeS => self.emit(Blt { rs1: rhs, rs2: lhs, imm: placeholder }),
                    // LtU -> branch to else if >= (unsigned)
                    CmpOp::LtU => self.emit(Bgeu { rs1: lhs, rs2: rhs, imm: placeholder }),
                    // GeU -> branch to else if < (unsigned)
                    CmpOp::GeU => self.emit(Bltu { rs1: lhs, rs2: rhs, imm: placeholder }),
                    // GtU -> branch to else if <= (unsigned)
                    CmpOp::GtU => self.emit(Bgeu { rs1: rhs, rs2: lhs, imm: placeholder }),
                    // LeU -> branch to else if > (unsigned)
                    CmpOp::LeU => self.emit(Bltu { rs1: rhs, rs2: lhs, imm: placeholder }),
                }

                self.patches.push((else_offset, *block_else));
            }

            IrInst::Branch { target } => {
                // Unconditional branch: jal x0, offset
                let offset = self.code.len();
                let placeholder = JImm21::new(0).unwrap();
                self.emit(Jal { rd: Gpr::ZERO, imm: placeholder });
                self.patches.push((offset, *target));
            }

            IrInst::Return { values } => {
                // Move return value(s) to calling convention registers (x9, x10, ...).
                for (i, &vreg) in values.iter().enumerate() {
                    let result = self.cache.ensure(vreg)?;
                    if result.needs_load {
                        self.emit_load(vreg, result.reg, func)?;
                    }
                    let ret_reg = PhysReg(9 + i as u8);
                    if result.reg != ret_reg {
                        self.emit_move(ret_reg, result.reg);
                    }
                }

                // ret = jalr x0, ra, 0
                let zero_imm = SImm12::new(0).unwrap();
                self.emit(Jalr {
                    rd: Gpr::ZERO,
                    rs1: Gpr(GprId::X1),
                    imm: zero_imm,
                });
            }

            IrInst::Call { func_idx, args, results, .. } => {
                // Move arguments to calling convention registers.
                for (i, &arg) in args.iter().enumerate() {
                    let r = self.cache.ensure(arg)?;
                    if r.needs_load {
                        self.emit_load(arg, r.reg, func)?;
                    }
                    let cc_reg = PhysReg(9 + i as u8);
                    if r.reg != cc_reg {
                        self.emit_move(cc_reg, r.reg);
                    }
                }

                // Flush dirty registers before the call.
                let dirty = self.cache.flush_dirty();
                for (phys, vreg) in dirty {
                    self.emit_store(vreg, phys, func)?;
                }

                let FunctionIdx::User(_idx) = func_idx;
                let entry_offset = self.labels.get(&BlockId::Entry)
                    .copied()
                    .unwrap_or(0);
                // Displacement in bytes for JAL.
                let disp = (entry_offset as i32 - self.code.len() as i32) * 4;
                let imm = JImm21::new(disp).map_err(|_| {
                    CodegenError::OffsetOutOfRange {
                        offset: disp as u32,
                        max: (1 << 20) - 1,
                    }
                })?;
                self.emit(Jal { rd: Gpr::RA, imm });

                // Invalidate all scratch regs — call clobbers everything.
                self.cache.invalidate_all();

                // Bind return values from calling convention registers.
                for (i, &res) in results.iter().enumerate() {
                    let cc_reg = PhysReg(9 + i as u8);
                    self.cache.bind(res, cc_reg);
                }
            }
        }
        Ok(())
    }

    /// Emit a move: `addi rd, rs, 0`.
    fn emit_move(&mut self, dst: PhysReg, src: PhysReg) {
        let zero_imm = SImm12::new(0).unwrap();
        self.emit(Addi {
            rd: Riscv64Backend::phys_to_gpr(dst),
            rs1: Riscv64Backend::phys_to_gpr(src),
            imm: zero_imm,
        });
    }

    /// Load an immediate value into a register.
    ///
    /// For values in the 12-bit signed range (-2048..2047), emits a single
    /// `addi rd, x0, imm`. For larger 32-bit values, emits `lui + addi`.
    fn emit_load_imm(&mut self, rd: Gpr, value: i64) {
        let val = value as i32;
        if val >= -2048 && val <= 2047 {
            self.emit(Addi {
                rd,
                rs1: Gpr::ZERO,
                imm: SImm12::new(val as i16).unwrap(),
            });
        } else {
            // lui loads bits [31:12]. addi adds bits [11:0].
            // If the lower 12 bits are negative (bit 11 set), lui needs
            // to be incremented by 1 to compensate for sign extension.
            let lower = ((val as i64) << 52 >> 52) as i32; // sign-extend lower 12 bits
            let upper = ((val as i64 - lower as i64) >> 12) as i32;
            let upper_imm = SImm20::new(upper)
                .expect("immediate too large for lui+addi");
            self.emit(Lui { rd, imm: upper_imm });
            if lower != 0 {
                self.emit(Addi {
                    rd,
                    rs1: rd,
                    imm: SImm12::new(lower as i16).unwrap(),
                });
            }
        }
    }

    /// Resolve a Register that must be physical.
    fn resolve_phys(&self, reg: Register) -> Result<PhysReg, CodegenError> {
        match reg {
            Register::Phys(n) => Ok(PhysReg(n)),
            Register::Virtual(v) => Err(CodegenError::InvalidRegister(
                format!("virtual register v{v} in lowering"),
            )),
        }
    }

    /// Emit a load from a VReg's canonical stack slot.
    fn emit_load(
        &mut self,
        vreg: VReg,
        dst: PhysReg,
        func: &IRFunction,
    ) -> Result<(), CodegenError> {
        let def = &self.vreg_defs[vreg.0 as usize];
        let vstack = &func.vstacks[def.slot.vstack.0 as usize];
        let base = self.resolve_phys(vstack.base)?;
        let offset = def.slot.byte_offset as i16;

        let imm = SImm12::new(offset).map_err(|_| CodegenError::OffsetOutOfRange {
            offset: def.slot.byte_offset,
            max: 2047,
        })?;

        match def.ty {
            IrType::I32 | IrType::F32 => {
                self.emit(Lw {
                    rd: Riscv64Backend::phys_to_gpr(dst),
                    rs1: Riscv64Backend::phys_to_gpr(base),
                    imm,
                });
            }
            _ => {
                self.emit(Ld {
                    rd: Riscv64Backend::phys_to_gpr(dst),
                    rs1: Riscv64Backend::phys_to_gpr(base),
                    imm,
                });
            }
        }
        Ok(())
    }

    /// Emit a store to a VReg's canonical stack slot.
    fn emit_store(
        &mut self,
        vreg: VReg,
        src: PhysReg,
        func: &IRFunction,
    ) -> Result<(), CodegenError> {
        let def = &self.vreg_defs[vreg.0 as usize];
        let vstack = &func.vstacks[def.slot.vstack.0 as usize];
        let base = self.resolve_phys(vstack.base)?;
        let offset = def.slot.byte_offset as i16;

        let imm = SImm12::new(offset).map_err(|_| CodegenError::OffsetOutOfRange {
            offset: def.slot.byte_offset,
            max: 2047,
        })?;

        match def.ty {
            IrType::I32 | IrType::F32 => {
                self.emit(Sw {
                    rs2: Riscv64Backend::phys_to_gpr(src),
                    rs1: Riscv64Backend::phys_to_gpr(base),
                    imm,
                });
            }
            _ => {
                self.emit(Sd {
                    rs2: Riscv64Backend::phys_to_gpr(src),
                    rs1: Riscv64Backend::phys_to_gpr(base),
                    imm,
                });
            }
        }
        Ok(())
    }

    /// Emit an ALU register-register instruction.
    fn emit_alu(
        &mut self,
        op: AluOp,
        dst: PhysReg,
        lhs: PhysReg,
        rhs: PhysReg,
        is_32: bool,
    ) {
        let rd = Riscv64Backend::phys_to_gpr(dst);
        let rs1 = Riscv64Backend::phys_to_gpr(lhs);
        let rs2 = Riscv64Backend::phys_to_gpr(rhs);

        match (op, is_32) {
            (AluOp::Add, false) => self.emit(Add { rd, rs1, rs2 }),
            (AluOp::Add, true) => self.emit(Addw { rd, rs1, rs2 }),
            (AluOp::Sub, false) => self.emit(Sub { rd, rs1, rs2 }),
            (AluOp::Sub, true) => self.emit(Subw { rd, rs1, rs2 }),
            (AluOp::Or, _) => self.emit(Or { rd, rs1, rs2 }),
            _ => {
                todo!("ALU op {op:?} not yet lowered for RISC-V");
            }
        }
    }

    /// Resolve all forward branch patches.
    ///
    /// RISC-V branches use two formats:
    /// - B-type (beq/bne/blt/bge/bltu/bgeu): 13-bit signed offset in bytes
    /// - J-type (jal): 21-bit signed offset in bytes
    ///
    /// We detect which format was used by checking the opcode field.
    fn resolve_patches(&mut self) -> Result<(), CodegenError> {
        for &(patch_offset, target) in &self.patches {
            let target_offset = self.labels.get(&target)
                .ok_or(CodegenError::UnresolvedLabel(target))?;

            // Displacement in words, then convert to bytes.
            let disp_words = *target_offset as i32 - patch_offset as i32;
            let disp_bytes = disp_words * 4;

            let old_word = self.code[patch_offset];
            let opcode = old_word & 0x7F;

            if opcode == 0x63 {
                // B-type branch: re-encode with correct offset.
                let imm = BImm13::new(disp_bytes as i16).map_err(|_| {
                    CodegenError::OffsetOutOfRange {
                        offset: disp_bytes as u32,
                        max: 4095,
                    }
                })?;
                // Preserve rs2, rs1, funct3, opcode — replace immediate bits.
                let base = old_word & 0x01FFF07F; // mask out imm fields
                self.code[patch_offset] = base | imm.encode_b_type();
            } else if opcode == 0x6F {
                // J-type (jal): re-encode with correct offset.
                let imm = JImm21::new(disp_bytes).map_err(|_| {
                    CodegenError::OffsetOutOfRange {
                        offset: disp_bytes as u32,
                        max: (1 << 20) - 1,
                    }
                })?;
                // Preserve rd and opcode — replace immediate bits.
                let base = old_word & 0x00000FFF; // rd[11:7] | opcode[6:0]
                self.code[patch_offset] = base | imm.encode_j_type();
            } else {
                return Err(CodegenError::InvalidRegister(
                    format!("unknown branch opcode 0x{opcode:02x} at offset {patch_offset}"),
                ));
            }
        }
        Ok(())
    }

    /// Convert the instruction buffer to bytes (little-endian).
    fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(self.code.len() * 4);
        for &word in &self.code {
            bytes.extend_from_slice(&word.to_le_bytes());
        }
        bytes
    }
}

/// Detect branch instructions in a RISC-V code buffer and return
/// [`BranchInfo`] entries.
///
/// Scans each 32-bit word for B-type branches (opcode 0x63) and
/// J-type jumps (opcode 0x6F/JAL, 0x67/JALR).
fn detect_branches(code: &[u32]) -> Vec<BranchInfo> {
    let mut branches = Vec::new();
    for (i, &word) in code.iter().enumerate() {
        let opcode = word & 0x7F;
        let source_byte = i * 4;

        match opcode {
            // B-type branches (beq, bne, blt, bge, bltu, bgeu)
            0x63 => {
                let offset = decode_b_imm(word);
                let target_byte = (source_byte as i64 + offset as i64) as usize;
                branches.push(BranchInfo {
                    offset: source_byte,
                    target: target_byte,
                    is_conditional: true,
                });
            }
            // JAL (J-type)
            0x6F => {
                let offset = decode_j_imm(word);
                let target_byte = (source_byte as i64 + offset as i64) as usize;
                let rd = (word >> 7) & 0x1F;
                // jal x0, ... is an unconditional jump (J pseudo-instruction)
                // jal ra, ... is a call
                branches.push(BranchInfo {
                    offset: source_byte,
                    target: target_byte,
                    is_conditional: false,
                });
                let _ = rd; // rd is used to distinguish call from jump, but both are branches
            }
            _ => {}
        }
    }
    branches
}

/// Decode B-type immediate from an encoded instruction word.
///
/// B-type layout: `imm[12|10:5] rs2 rs1 funct3 imm[4:1|11] opcode`
fn decode_b_imm(word: u32) -> i32 {
    let bit12 = (word >> 31) & 1;
    let bits10_5 = (word >> 25) & 0x3F;
    let bits4_1 = (word >> 8) & 0xF;
    let bit11 = (word >> 7) & 1;
    let raw = (bit12 << 12) | (bit11 << 11) | (bits10_5 << 5) | (bits4_1 << 1);
    // Sign-extend from 13 bits.
    ((raw as i32) << 19) >> 19
}

/// Decode J-type immediate from an encoded instruction word.
///
/// J-type layout: `imm[20|10:1|11|19:12] rd opcode`
fn decode_j_imm(word: u32) -> i32 {
    let bit20 = (word >> 31) & 1;
    let bits10_1 = (word >> 21) & 0x3FF;
    let bit11 = (word >> 20) & 1;
    let bits19_12 = (word >> 12) & 0xFF;
    let raw = (bit20 << 20) | (bits19_12 << 12) | (bit11 << 11) | (bits10_1 << 1);
    // Sign-extend from 21 bits.
    ((raw as i32) << 11) >> 11
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CodeBuilder, FunctionBuilder, VStack};

    #[test]
    fn use_isa_reg_fixed_roles() {
        let mut backend = Riscv64Backend::new();

        let fp = backend.use_isa_reg("fp", IsaReg::FramePointer);
        let ra = backend.use_isa_reg("ra", IsaReg::ReturnAddress);
        let sp = backend.use_isa_reg("sp", IsaReg::StackPointer);

        assert_eq!(fp, Register::Phys(8));   // s0/fp
        assert_eq!(ra, Register::Phys(1));   // ra
        assert_eq!(sp, Register::Phys(19));  // s3

        let scratch = backend.scratch();
        assert!(!scratch.contains(&PhysReg(8)));
        assert!(!scratch.contains(&PhysReg(1)));
        assert!(!scratch.contains(&PhysReg(19)));
    }

    #[test]
    fn use_isa_reg_define64() {
        let mut backend = Riscv64Backend::new();

        backend.use_isa_reg("fp", IsaReg::FramePointer);
        backend.use_isa_reg("ra", IsaReg::ReturnAddress);
        backend.use_isa_reg("sp", IsaReg::StackPointer);

        // After removing x1, x8, x19: pool starts with [2, 5, 6, 7, 9, 10, ...]
        let fuel = backend.use_isa_reg("fuel", IsaReg::Define64(0));
        // Define64(0) -> first in remaining pool = x2
        assert_eq!(fuel, Register::Phys(2));

        let ctx = backend.use_isa_reg("ctx", IsaReg::Define64(-1));
        // Define64(-1) -> last = x31
        assert_eq!(ctx, Register::Phys(31));

        assert!(!backend.scratch().contains(&PhysReg(2)));
        assert!(!backend.scratch().contains(&PhysReg(31)));
    }

    #[test]
    fn no_pool_overlap() {
        let mut backend = Riscv64Backend::new();

        backend.use_isa_reg("fp", IsaReg::FramePointer);
        backend.use_isa_reg("ra", IsaReg::ReturnAddress);
        backend.use_isa_reg("sp", IsaReg::StackPointer);
        backend.use_isa_reg("fuel", IsaReg::Define64(0));
        backend.use_isa_reg("ctx", IsaReg::Define64(-1));

        for (_, phys) in &backend.assignments {
            assert!(
                !backend.scratch().contains(phys),
                "assigned reg {phys:?} found in scratch pool"
            );
        }

        let mut seen = std::collections::HashSet::new();
        for reg in backend.scratch() {
            assert!(seen.insert(reg), "duplicate in scratch pool: {reg:?}");
        }
    }

    #[test]
    fn pool_excludes_x0_x3_x4() {
        let backend = Riscv64Backend::new();
        let scratch = backend.scratch();
        assert!(!scratch.contains(&PhysReg(0)), "x0 (zero) should not be in pool");
        assert!(!scratch.contains(&PhysReg(3)), "x3 (gp) should not be in pool");
        assert!(!scratch.contains(&PhysReg(4)), "x4 (tp) should not be in pool");
    }

    #[test]
    fn prologue_sd_pre_decrement() {
        let mut backend = Riscv64Backend::new();

        let _fp = backend.use_isa_reg("fp", IsaReg::FramePointer);
        let ra = backend.use_isa_reg("ra", IsaReg::ReturnAddress);
        let fsp = backend.use_isa_reg("fsp", IsaReg::StackPointer);

        let mut f = FunctionBuilder::new();

        let fibre = f.define_vstack(VStack {
            base: fsp,
            offset: 0,
        });

        f.entry_block(crate::BlockId::Entry);
        f.push_i64(fibre, Value::Reg(ra));

        let mut cb = CodeBuilder::new();
        f.build(&mut cb);

        let func = &cb.functions()[0];
        let code = backend.lower(func).unwrap();

        // Should emit: addi s3, s3, -8; sd ra, 0(s3)
        // That's 2 instructions = 8 bytes.
        assert_eq!(code.len(), 8);

        let word0 = u32::from_le_bytes([code[0], code[1], code[2], code[3]]);
        let word1 = u32::from_le_bytes([code[4], code[5], code[6], code[7]]);

        // addi x19, x19, -8
        let expected_addi = Addi {
            rd: Gpr(GprId::X19),
            rs1: Gpr(GprId::X19),
            imm: SImm12::new(-8).unwrap(),
        };
        assert_eq!(
            word0,
            expected_addi.encode_word(),
            "word0: got 0x{word0:08X}, expected 0x{:08X}",
            expected_addi.encode_word()
        );

        // sd x1, 0(x19)
        let expected_sd = Sd {
            rs2: Gpr(GprId::X1),
            rs1: Gpr(GprId::X19),
            imm: SImm12::new(0).unwrap(),
        };
        assert_eq!(
            word1,
            expected_sd.encode_word(),
            "word1: got 0x{word1:08X}, expected 0x{:08X}",
            expected_sd.encode_word()
        );
    }

    #[test]
    fn b_imm_roundtrip() {
        // Verify that encoding then decoding a B-type immediate produces
        // the original value.
        for offset in [-4096i16, -8, 0, 8, 16, 128, 4094] {
            let imm = BImm13::new(offset).unwrap();
            let encoded = imm.encode_b_type() | 0x63; // add opcode to make it a valid word
            let decoded = decode_b_imm(encoded);
            assert_eq!(decoded, offset as i32, "B-imm roundtrip failed for {offset}");
        }
    }

    #[test]
    fn j_imm_roundtrip() {
        for offset in [-(1i32 << 20), -200, 0, 100, (1 << 20) - 2] {
            let imm = JImm21::new(offset).unwrap();
            let encoded = imm.encode_j_type() | 0x6F;
            let decoded = decode_j_imm(encoded);
            assert_eq!(decoded, offset, "J-imm roundtrip failed for {offset}");
        }
    }
}
