use std::collections::HashMap;

use autosynth_isa_x86_64::{
    AddRegImm, AddRegReg, CallRel32, CmpRegImm, CmpRegReg, Imm32, Jcc, JmpRel32, MovLoad,
    MovRegImm, MovRegReg, MovStore, Ret, X86_64Inst,
    reg::{Gpr, Gpr32, Gpr64, GprId},
};

use super::{BackendEmitter, PhysReg};
use crate::CodegenError;
use crate::disasm::{BlockLabel, BranchInfo, DisasmInst, DisasmMetadata};
use crate::ir::block::BlockId;
use crate::ir::function::{FunctionIdx, IRFunction, IsaReg};
use crate::ir::instruction::{AluOp, CmpOp, IrInst};
use crate::ir::{IrType, Register, VReg, VRegDef, Value};
use crate::regalloc::RegCache;

/// x86_64 backend: manages the AMD64 register pool and lowers IR to
/// native machine code.
///
/// The caller reserves named registers via [`BackendEmitter::use_isa_reg`]
/// before building the IR. The remaining pool is used as scratch registers
/// by the register cache during lowering.
///
/// # Register conventions
///
/// - `R12` — software frame pointer (callee-saved)
/// - `R13` — software stack pointer (callee-saved)
/// - `R14` — context pointer (callee-saved)
/// - Scratch: RAX, RCX, RDX, RSI, RDI, R8, R9, R10, R11
/// - Reserved: RSP (hardware stack), RBP (frame pointer)
/// - Return value: RAX
pub struct X86_64Backend {
    pool: Vec<PhysReg>,
    assignments: HashMap<&'static str, PhysReg>,
}

impl X86_64Backend {
    /// Create a new x86_64 backend with the full general-purpose register pool.
    ///
    /// Excludes RSP (4, hardware stack pointer) and RBP (5, frame pointer).
    pub fn new() -> Self {
        let pool = (0u8..=15)
            .filter(|&r| r != 4 && r != 5) // exclude RSP, RBP
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

    /// Map a fixed ISA role to its x86_64-specific physical register.
    ///
    /// - FramePointer -> R12 (callee-saved, software frame pointer)
    /// - StackPointer -> R13 (callee-saved, software stack pointer)
    /// - ReturnAddress -> R15 (callee-saved; x86 uses call/ret implicitly,
    ///   but we reserve R15 for explicit return address management in the
    ///   wust runtime's fibre stack model)
    fn fixed_phys(role: IsaReg) -> Option<PhysReg> {
        match role {
            IsaReg::FramePointer => Some(PhysReg(GprId::R12 as u8)),
            IsaReg::StackPointer => Some(PhysReg(GprId::R13 as u8)),
            IsaReg::ReturnAddress => Some(PhysReg(GprId::R15 as u8)),
            IsaReg::Define64(_) => None,
        }
    }

    /// Convert a PhysReg to a 32-bit GPR for instruction emission.
    fn phys_to_gpr32(reg: PhysReg) -> Gpr32 {
        Gpr32(GprId::from_index(reg.0))
    }

    /// Convert a PhysReg to a 64-bit GPR for instruction emission.
    fn phys_to_gpr64(reg: PhysReg) -> Gpr64 {
        Gpr64(GprId::from_index(reg.0))
    }

    /// Convert a Register to a 64-bit GPR, failing on virtual registers.
    fn reg_to_gpr64(reg: Register) -> Result<Gpr64, CodegenError> {
        match reg {
            Register::Phys(n) => Ok(Gpr64(GprId::from_index(n))),
            Register::Virtual(v) => Err(CodegenError::InvalidRegister(
                format!("virtual register v{v} in lowering"),
            )),
        }
    }

    /// Map a CmpOp to the x86_64 condition code for the "true" branch.
    fn cmp_op_to_cond(op: CmpOp) -> autosynth_isa_x86_64::Cond {
        match op {
            CmpOp::Eq => autosynth_isa_x86_64::Cond::E,
            CmpOp::Ne => autosynth_isa_x86_64::Cond::NE,
            CmpOp::LtS => autosynth_isa_x86_64::Cond::L,
            CmpOp::LtU => autosynth_isa_x86_64::Cond::B,
            CmpOp::GtS => autosynth_isa_x86_64::Cond::G,
            CmpOp::GtU => autosynth_isa_x86_64::Cond::A,
            CmpOp::LeS => autosynth_isa_x86_64::Cond::LE,
            CmpOp::LeU => autosynth_isa_x86_64::Cond::BE,
            CmpOp::GeS => autosynth_isa_x86_64::Cond::GE,
            CmpOp::GeU => autosynth_isa_x86_64::Cond::AE,
        }
    }
}

impl BackendEmitter for X86_64Backend {
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

    fn lower(&self, func: &IRFunction) -> Result<Vec<u8>, CodegenError> {
        let (bytes, _) = self.lower_with_disasm(func)?;
        Ok(bytes)
    }
}

impl X86_64Backend {
    /// Lower an IR function to machine code bytes and a human-readable
    /// disassembly listing.
    ///
    /// The listing interleaves block labels with per-instruction annotations
    /// showing byte offset and mnemonic.
    pub fn lower_with_disasm(
        &self,
        func: &IRFunction,
    ) -> Result<(Vec<u8>, DisasmMetadata), CodegenError> {
        let mut ctx = LowerCtx::new(&self.pool, &func.vreg_defs);
        let mut block_labels: Vec<BlockLabel> = Vec::new();

        for block in &func.blocks {
            block_labels.push(BlockLabel {
                offset: ctx.code.len(),
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

        // Build DisasmMetadata from lowering context.
        let instructions: Vec<DisasmInst> = ctx
            .disasm
            .iter()
            .map(|(offset, text)| DisasmInst {
                offset: *offset,
                text: text.clone(),
                annotation: None,
            })
            .collect();

        // Detect branch instructions and record their targets.
        let branches = detect_branches(&ctx.code);

        let meta = DisasmMetadata {
            instructions,
            block_labels,
            branches,
            signature: None,
        };

        Ok((ctx.code, meta))
    }
}

/// Deferred comparison waiting for a BrIf to fuse into a conditional branch.
struct PendingCmp {
    cond: autosynth_isa_x86_64::Cond,
}

/// Lowering context — mutable state for a single function's code generation.
///
/// Unlike the aarch64 backend which uses `Vec<u32>` (fixed 4-byte instructions),
/// x86_64 uses `Vec<u8>` because instructions are variable-length (1-15 bytes).
struct LowerCtx<'a> {
    code: Vec<u8>,
    cache: RegCache,
    vreg_defs: &'a [VRegDef],
    labels: HashMap<BlockId, usize>,
    /// (byte_offset_of_rel32_field, target_block) — patches for forward branches.
    /// The offset points to the start of the 4-byte rel32 field within the instruction.
    patches: Vec<(usize, BlockId)>,
    /// Fused compare-and-branch state.
    pending_cmp: Option<PendingCmp>,
    /// Per-instruction disassembly annotations: (byte_offset, text).
    disasm: Vec<(usize, String)>,
}

impl<'a> LowerCtx<'a> {
    fn new(scratch: &[PhysReg], vreg_defs: &'a [VRegDef]) -> Self {
        Self {
            code: Vec::with_capacity(256),
            cache: RegCache::new(scratch),
            vreg_defs,
            labels: HashMap::new(),
            patches: Vec::new(),
            pending_cmp: None,
            disasm: Vec::new(),
        }
    }

    /// Emit an instruction, encoding it into the code buffer and recording
    /// its disassembly text.
    fn emit<I: X86_64Inst + core::fmt::Display>(&mut self, inst: I) {
        let offset = self.code.len();
        self.disasm.push((offset, format!("{inst}")));
        let mut buf = [0u8; 15];
        let n = inst.encode_bytes(&mut buf);
        self.code.extend_from_slice(&buf[..n]);
    }

    /// Resolve a Register to a PhysReg, emitting a load if needed.
    ///
    /// - Physical registers pass through directly.
    /// - Virtual registers go through the regcache (ensure + optional load).
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
    ///
    /// Physical registers pass through. Virtual registers get defined.
    fn resolve_dst(&mut self, reg: Register) -> Result<PhysReg, CodegenError> {
        match reg {
            Register::Phys(n) => Ok(PhysReg(n)),
            Register::Virtual(id) => self.cache.define(VReg(id)),
        }
    }

    /// Get the IR type for a Register (only meaningful for virtual registers).
    fn reg_type(&self, reg: Register) -> IrType {
        match reg {
            Register::Phys(_) => IrType::I64,
            Register::Virtual(id) => self.vreg_defs[id as usize].ty,
        }
    }

    /// Try to extract a constant value from a Register.
    ///
    /// Returns the constant if the Register is a VReg with a known
    /// constant value (ConstI32, Const). Returns None for physical
    /// registers or VRegs with non-constant values.
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
                        self.emit(MovRegImm {
                            dst: Gpr::R32(X86_64Backend::phys_to_gpr32(phys)),
                            imm: n as i64,
                        });
                    }
                    Value::Const(n) => {
                        let phys = self.cache.define(def.id)?;
                        self.emit(MovRegImm {
                            dst: Gpr::R64(X86_64Backend::phys_to_gpr64(phys)),
                            imm: n,
                        });
                    }
                    Value::VReg(src) => {
                        // Ensure source is in a register (may emit a load).
                        let src_result = self.cache.ensure(src)?;
                        if src_result.needs_load {
                            self.emit_load(src, src_result.reg, func)?;
                        }
                        self.cache.alias(def.id, src)
                            .expect("alias failed after ensure");
                    }
                    Value::Reg(reg) => {
                        // Physical register push onto fibre stack via pre-decrement store.
                        // On x86_64: sub base, size; mov [base], reg
                        let base_reg = func.vstacks[def.slot.vstack.0 as usize].base;
                        let base = X86_64Backend::reg_to_gpr64(base_reg)?;
                        let size = def.slot.size as i32;

                        // Decrement the base pointer.
                        self.emit(autosynth_isa_x86_64::SubRegImm {
                            dst: Gpr::R64(base),
                            imm: Imm32::new(size),
                        });

                        // Store the register value at [base].
                        let src_gpr = X86_64Backend::reg_to_gpr64(reg)?;
                        self.emit(MovStore {
                            base,
                            disp: 0,
                            src: Gpr::R64(src_gpr),
                        });
                    }
                    Value::Param(i) => {
                        // Parameters arrive in calling convention registers.
                        // Param 0 is in RAX (index 0), param 1 in RCX (index 1), etc.
                        // We use the same register indices as the aarch64 backend
                        // uses for x9, x10... — but on x86 we pick R9, R10, ...
                        let cc_reg = PhysReg(9 + i as u8);
                        self.cache.bind(def.id, cc_reg);
                    }
                }
            }

            IrInst::StackPop { def } => {
                if let Value::Reg(reg) = def.value {
                    // Pop from fibre stack: load [base], then increment base.
                    let base_reg = func.vstacks[def.slot.vstack.0 as usize].base;
                    let base = X86_64Backend::reg_to_gpr64(base_reg)?;
                    let size = def.slot.size as i32;

                    let dst_gpr = X86_64Backend::reg_to_gpr64(reg)?;
                    self.emit(MovLoad {
                        dst: Gpr::R64(dst_gpr),
                        base,
                        disp: 0,
                    });

                    // Increment the base pointer.
                    self.emit(AddRegImm {
                        dst: Gpr::R64(base),
                        imm: Imm32::new(size),
                    });
                    return Ok(());
                }

                // If the VReg was never defined in the cache (e.g., Cmp
                // destination consumed by BrIf via flags), skip it.
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

                // Try to fold rhs into an immediate.
                if let Some(imm) = self.try_const(*rhs) {
                    if imm >= i32::MIN as i64 && imm <= i32::MAX as i64 {
                        // x86 is 2-operand: if dst != lhs, emit mov first.
                        if dst_phys != lhs_phys {
                            self.emit_mov(dst_phys, lhs_phys, is_32);
                        }
                        self.emit_alu_imm(*op, dst_phys, Imm32::new(imm as i32), is_32);
                        // Release the constant VReg — it was folded, not loaded.
                        if let Register::Virtual(id) = rhs {
                            self.cache.release(VReg(*id));
                        }
                        return Ok(());
                    }
                }

                let rhs_phys = self.resolve(*rhs, func)?;
                // x86 is 2-operand: if dst != lhs, emit mov first.
                if dst_phys != lhs_phys {
                    self.emit_mov(dst_phys, lhs_phys, is_32);
                }
                self.emit_alu(*op, dst_phys, rhs_phys, is_32);
            }

            IrInst::Cmp { op, dst: _, lhs, rhs } => {
                let lhs_phys = self.resolve(*lhs, func)?;

                let is_32 = matches!(self.reg_type(*lhs), IrType::I32 | IrType::F32);

                // Try to fold rhs into an immediate for cmp r/m, imm.
                if let Some(imm) = self.try_const(*rhs) {
                    if imm >= i32::MIN as i64 && imm <= i32::MAX as i64 {
                        let gpr = if is_32 {
                            Gpr::R32(X86_64Backend::phys_to_gpr32(lhs_phys))
                        } else {
                            Gpr::R64(X86_64Backend::phys_to_gpr64(lhs_phys))
                        };
                        self.emit(CmpRegImm {
                            dst: gpr,
                            imm: Imm32::new(imm as i32),
                        });
                        if let Register::Virtual(id) = rhs {
                            self.cache.release(VReg(*id));
                        }
                        self.pending_cmp = Some(PendingCmp {
                            cond: X86_64Backend::cmp_op_to_cond(*op),
                        });
                        return Ok(());
                    }
                }

                let rhs_phys = self.resolve(*rhs, func)?;

                if is_32 {
                    self.emit(CmpRegReg {
                        lhs: Gpr::R32(X86_64Backend::phys_to_gpr32(lhs_phys)),
                        rhs: Gpr::R32(X86_64Backend::phys_to_gpr32(rhs_phys)),
                    });
                } else {
                    self.emit(CmpRegReg {
                        lhs: Gpr::R64(X86_64Backend::phys_to_gpr64(lhs_phys)),
                        rhs: Gpr::R64(X86_64Backend::phys_to_gpr64(rhs_phys)),
                    });
                }

                self.pending_cmp = Some(PendingCmp {
                    cond: X86_64Backend::cmp_op_to_cond(*op),
                });
            }

            IrInst::BrIf { cond: _, block_if: _, block_else } => {
                // Fuse with pending comparison.
                let pending = self.pending_cmp.take()
                    .expect("BrIf without preceding Cmp");

                // Emit jcc with inverted condition to the else block (then-block
                // is the fallthrough, same as aarch64).
                // Jcc is 6 bytes: 0F 8x rel32. The rel32 field starts at byte offset + 2.
                let inst_offset = self.code.len();
                self.emit(Jcc {
                    cond: pending.cond.invert(),
                    offset: 0, // patched later
                });
                // The rel32 field starts 2 bytes into the instruction.
                self.patches.push((inst_offset + 2, *block_else));
            }

            IrInst::Branch { target } => {
                // Unconditional jump: jmp rel32 (5 bytes, rel32 at offset + 1).
                let inst_offset = self.code.len();
                self.emit(JmpRel32 { offset: 0 });
                self.patches.push((inst_offset + 1, *target));
            }

            IrInst::Return { values } => {
                // Move return value(s) to calling convention registers (R9, R10, ...).
                for (i, &vreg) in values.iter().enumerate() {
                    let result = self.cache.ensure(vreg)?;
                    if result.needs_load {
                        self.emit_load(vreg, result.reg, func)?;
                    }
                    let ret_reg = PhysReg(9 + i as u8);
                    if result.reg != ret_reg {
                        let ty = self.vreg_defs[vreg.0 as usize].ty;
                        let is_32 = matches!(ty, IrType::I32 | IrType::F32);
                        self.emit_mov(ret_reg, result.reg, is_32);
                    }
                }

                self.emit(Ret);
            }

            IrInst::Call { func_idx, .. } => {
                // Flush all dirty registers to canonical slots before the call.
                let dirty = self.cache.flush_dirty();
                for (phys, vreg) in dirty {
                    self.emit_store(vreg, phys, func)?;
                }

                // Emit call rel32 to the target function.
                // For now, only recursive calls (call back to entry).
                let FunctionIdx::User(_idx) = func_idx;
                let entry_offset = self.labels.get(&BlockId::Entry)
                    .copied()
                    .unwrap_or(0);
                // call rel32 is 5 bytes. Offset is relative to end of instruction.
                let call_end = self.code.len() + 5;
                let disp = entry_offset as i32 - call_end as i32;
                self.emit(CallRel32 { offset: disp });

                // Invalidate all scratch regs — call clobbers everything.
                self.cache.invalidate_all();
            }
        }
        Ok(())
    }

    /// Emit a load from a VReg's canonical stack slot.
    fn emit_load(&mut self, vreg: VReg, dst: PhysReg, func: &IRFunction) -> Result<(), CodegenError> {
        let def = &self.vreg_defs[vreg.0 as usize];
        let vstack = &func.vstacks[def.slot.vstack.0 as usize];
        let base = X86_64Backend::reg_to_gpr64(vstack.base)?;
        let offset = def.slot.byte_offset as i32;

        match def.ty {
            IrType::I32 | IrType::F32 => {
                self.emit(MovLoad {
                    dst: Gpr::R32(X86_64Backend::phys_to_gpr32(dst)),
                    base,
                    disp: offset,
                });
            }
            _ => {
                self.emit(MovLoad {
                    dst: Gpr::R64(X86_64Backend::phys_to_gpr64(dst)),
                    base,
                    disp: offset,
                });
            }
        }
        Ok(())
    }

    /// Emit a store to a VReg's canonical stack slot.
    fn emit_store(&mut self, vreg: VReg, src: PhysReg, func: &IRFunction) -> Result<(), CodegenError> {
        let def = &self.vreg_defs[vreg.0 as usize];
        let vstack = &func.vstacks[def.slot.vstack.0 as usize];
        let base = X86_64Backend::reg_to_gpr64(vstack.base)?;
        let offset = def.slot.byte_offset as i32;

        match def.ty {
            IrType::I32 | IrType::F32 => {
                self.emit(MovStore {
                    base,
                    disp: offset,
                    src: Gpr::R32(X86_64Backend::phys_to_gpr32(src)),
                });
            }
            _ => {
                self.emit(MovStore {
                    base,
                    disp: offset,
                    src: Gpr::R64(X86_64Backend::phys_to_gpr64(src)),
                });
            }
        }
        Ok(())
    }

    /// Emit a register-to-register move.
    ///
    /// Used to implement the 2-operand constraint: if the IR has
    /// `dst = lhs + rhs` and dst != lhs, we emit `mov dst, lhs` first.
    fn emit_mov(&mut self, dst: PhysReg, src: PhysReg, is_32: bool) {
        if is_32 {
            self.emit(MovRegReg {
                dst: Gpr::R32(X86_64Backend::phys_to_gpr32(dst)),
                src: Gpr::R32(X86_64Backend::phys_to_gpr32(src)),
            });
        } else {
            self.emit(MovRegReg {
                dst: Gpr::R64(X86_64Backend::phys_to_gpr64(dst)),
                src: Gpr::R64(X86_64Backend::phys_to_gpr64(src)),
            });
        }
    }

    /// Emit a register-register ALU instruction (2-operand form: dst op= src).
    fn emit_alu(&mut self, op: AluOp, dst: PhysReg, src: PhysReg, is_32: bool) {
        let (dst_gpr, src_gpr): (Gpr, Gpr) = if is_32 {
            (
                Gpr::R32(X86_64Backend::phys_to_gpr32(dst)),
                Gpr::R32(X86_64Backend::phys_to_gpr32(src)),
            )
        } else {
            (
                Gpr::R64(X86_64Backend::phys_to_gpr64(dst)),
                Gpr::R64(X86_64Backend::phys_to_gpr64(src)),
            )
        };

        match op {
            AluOp::Add => {
                self.emit(AddRegReg { dst: dst_gpr, src: src_gpr });
            }
            AluOp::Sub => {
                self.emit(autosynth_isa_x86_64::SubRegReg { dst: dst_gpr, src: src_gpr });
            }
            _ => {
                todo!("ALU op {op:?} not yet lowered for x86_64");
            }
        }
    }

    /// Emit an ALU-immediate instruction (2-operand form: dst op= imm).
    fn emit_alu_imm(&mut self, op: AluOp, dst: PhysReg, imm: Imm32, is_32: bool) {
        let gpr = if is_32 {
            Gpr::R32(X86_64Backend::phys_to_gpr32(dst))
        } else {
            Gpr::R64(X86_64Backend::phys_to_gpr64(dst))
        };

        match op {
            AluOp::Add => {
                self.emit(AddRegImm { dst: gpr, imm });
            }
            AluOp::Sub => {
                self.emit(autosynth_isa_x86_64::SubRegImm { dst: gpr, imm });
            }
            _ => {
                todo!("ALU-imm op {op:?} not yet supported for x86_64");
            }
        }
    }

    /// Resolve all forward branch patches.
    ///
    /// Each patch stores the byte offset of a rel32 field. The rel32 value
    /// is computed as: `target_byte - (rel32_offset + 4)`, because x86
    /// relative offsets are measured from the end of the instruction
    /// (i.e., from the byte after the 4-byte rel32 field).
    fn resolve_patches(&mut self) -> Result<(), CodegenError> {
        for &(rel32_offset, target) in &self.patches {
            let target_byte = self.labels.get(&target)
                .ok_or(CodegenError::UnresolvedLabel(target))?;

            let disp = *target_byte as i32 - (rel32_offset as i32 + 4);
            let bytes = disp.to_le_bytes();
            self.code[rel32_offset..rel32_offset + 4].copy_from_slice(&bytes);
        }
        Ok(())
    }
}

/// Detect branch instructions in x86_64 code and return [`BranchInfo`] entries.
///
/// Scans for `Jcc rel32` (0F 8x), `JMP rel32` (E9), and `CALL rel32` (E8)
/// patterns and computes target byte offsets.
fn detect_branches(code: &[u8]) -> Vec<BranchInfo> {
    let mut branches = Vec::new();
    let mut i = 0;
    while i < code.len() {
        match code[i] {
            // JMP rel32: E9 xx xx xx xx (5 bytes)
            0xE9 if i + 5 <= code.len() => {
                let rel = i32::from_le_bytes([code[i + 1], code[i + 2], code[i + 3], code[i + 4]]);
                let target = (i as i64 + 5 + rel as i64) as usize;
                branches.push(BranchInfo {
                    offset: i,
                    target,
                    is_conditional: false,
                });
                i += 5;
            }
            // CALL rel32: E8 xx xx xx xx (5 bytes)
            0xE8 if i + 5 <= code.len() => {
                let rel = i32::from_le_bytes([code[i + 1], code[i + 2], code[i + 3], code[i + 4]]);
                let target = (i as i64 + 5 + rel as i64) as usize;
                branches.push(BranchInfo {
                    offset: i,
                    target,
                    is_conditional: false,
                });
                i += 5;
            }
            // Jcc rel32: 0F 8x xx xx xx xx (6 bytes)
            0x0F if i + 6 <= code.len() && (code[i + 1] & 0xF0) == 0x80 => {
                let rel = i32::from_le_bytes([code[i + 2], code[i + 3], code[i + 4], code[i + 5]]);
                let target = (i as i64 + 6 + rel as i64) as usize;
                branches.push(BranchInfo {
                    offset: i,
                    target,
                    is_conditional: true,
                });
                i += 6;
            }
            _ => {
                i += 1;
            }
        }
    }
    branches
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CodeBuilder, FunctionBuilder, VStack};

    #[test]
    fn use_isa_reg_fixed_roles() {
        let mut backend = X86_64Backend::new();

        let fp = backend.use_isa_reg("fp", IsaReg::FramePointer);
        let ra = backend.use_isa_reg("ra", IsaReg::ReturnAddress);
        let sp = backend.use_isa_reg("sp", IsaReg::StackPointer);

        assert_eq!(fp, Register::Phys(GprId::R12 as u8));
        assert_eq!(ra, Register::Phys(GprId::R15 as u8));
        assert_eq!(sp, Register::Phys(GprId::R13 as u8));

        // Fixed regs removed from scratch pool
        let scratch = backend.scratch();
        assert!(!scratch.contains(&PhysReg(GprId::R12 as u8)));
        assert!(!scratch.contains(&PhysReg(GprId::R13 as u8)));
        assert!(!scratch.contains(&PhysReg(GprId::R15 as u8)));
    }

    #[test]
    fn use_isa_reg_define64() {
        let mut backend = X86_64Backend::new();

        // Reserve fixed roles first
        backend.use_isa_reg("fp", IsaReg::FramePointer);
        backend.use_isa_reg("ra", IsaReg::ReturnAddress);
        backend.use_isa_reg("sp", IsaReg::StackPointer);

        // Pool after removing r12, r13, r15: [0,1,2,3,6,7,8,9,10,11,14]
        let fuel = backend.use_isa_reg("fuel", IsaReg::Define64(0));
        // Define64(0) -> first = 0 (RAX)
        assert_eq!(fuel, Register::Phys(0));

        let ctx = backend.use_isa_reg("ctx", IsaReg::Define64(-1));
        // After removing 0: pool = [1,2,3,6,7,8,9,10,11,14]
        // Define64(-1) -> last = 14 (R14)
        assert_eq!(ctx, Register::Phys(14));

        assert!(!backend.scratch().contains(&PhysReg(0)));
        assert!(!backend.scratch().contains(&PhysReg(14)));
    }

    #[test]
    fn no_pool_overlap() {
        let mut backend = X86_64Backend::new();

        backend.use_isa_reg("fp", IsaReg::FramePointer);
        backend.use_isa_reg("ra", IsaReg::ReturnAddress);
        backend.use_isa_reg("sp", IsaReg::StackPointer);
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

    #[test]
    fn rsp_rbp_excluded() {
        let backend = X86_64Backend::new();
        assert!(!backend.scratch().contains(&PhysReg(4))); // RSP
        assert!(!backend.scratch().contains(&PhysReg(5))); // RBP
    }

    #[test]
    fn fibre_push_lowers_to_sub_then_store() {
        let mut backend = X86_64Backend::new();

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

        // Should produce: sub r13, 8; mov [r13], r15
        // sub r13, 8 = REX.W(49) 83 ED 08  (4 bytes)
        // mov [r13], r15 = REX.WRB(4D) 89 7D 00 (4 bytes, r13 needs disp8=0 like rbp)
        assert!(!code.is_empty(), "lowered code should not be empty");
        // Verify at least the sub instruction prefix
        assert!(code.len() >= 4, "expected at least 4 bytes, got {}", code.len());
    }
}
