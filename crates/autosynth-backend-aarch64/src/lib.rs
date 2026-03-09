//! AArch64 backend — pure instruction selection for ARM64.
//!
//! This crate translates IR operations into AArch64 machine code.
//! It does NOT manage register allocation, spilling, or materialization.
//! All operand resolution goes through [`autosynth_lower::LowerCtx`].

use autosynth_backend::{BackendEmitter, LowerError, MachineConfig};
use autosynth_ir::{AluOp, CompOp, FunctionIdx, IrInst, Operand, Register};
use autosynth_isa::{IsaReg, PReg, PRegOr, UImm12, Width};
use autosynth_isa_aarch64::{
    Aarch64Inst, AddImm, AddReg, BCond, Bl, Cond, LdrUoff, StrUoff, SubImm, SubReg, SubsImm,
    SubsReg,
    reg::{Gpr, GprId, GprOrSp, GprOrZr, WGpr, XGpr},
};
use autosynth_lower::{self, LowerCtx, LowerCtxExt};

/// A saved patch point — the byte offset of an instruction that needs
/// its offset field rewritten after all blocks are laid out.
struct Patch {
    /// Byte offset of the instruction in the code buffer.
    offset: usize,
    /// The original IR instruction (contains the target BlockId or FunctionIdx).
    inst: IrInst,
    /// The condition code used for b.cond, if applicable.
    cond: Option<Cond>,
}

/// AArch64 backend — stateful instruction selector.
///
/// Uses `pending` to fuse compare+branch sequences: when an
/// `Alu(Comp)` arrives, the condition code is stored. A subsequent
/// `BrIf` consumes it and emits `b.cond` with the inverted condition.
pub struct Aarch64Backend {
    pending: Option<Operation>,
    /// Branch/call instructions that need offset patching after layout.
    patches: Vec<Patch>,
}

/// A deferred operation with its debugger group index.
#[derive(Debug)]
struct Operation {
    /// The debugger group this operation belongs to — restored when emitting.
    dbg_group_idx: usize,
    op: CompoundOperation,
}

#[derive(Debug)]
enum CompoundOperation {
    /// A single deferred instruction, waiting to see if the next instruction can fuse with it.
    Base(IrInst),
}

fn fixed_aarch64(role: IsaReg) -> Option<PReg> {
    match role {
        IsaReg::FramePointer => Some(PReg(29)),
        IsaReg::StackPointer => Some(PReg(28)),
        IsaReg::ReturnAddress => Some(PReg(30)),
        IsaReg::Alloc64(_) => None,
    }
}

impl BackendEmitter for Aarch64Backend {
    fn new() -> (Self, MachineConfig) {
        let pool = (0u8..=30).filter(|&r| r != 18).map(PReg).collect();
        let config = MachineConfig::new(pool, fixed_aarch64);
        let backend = Self {
            pending: None,
            patches: Vec::new(),
        };
        (backend, config)
    }

    fn lower(&mut self, ctx: &mut impl LowerCtx, inst: IrInst) -> Result<(), LowerError> {
        let mut dbg_group_idx = 0;
        autosynth_lower::dbg(|dbg| dbg_group_idx = dbg.current_group());

        match self.pending.take() {
            None => {
                self.pending = Some(Operation {
                    dbg_group_idx,
                    op: CompoundOperation::Base(inst),
                });
                Ok(())
            }
            Some(pending) => self.fuse(ctx, pending, inst, dbg_group_idx),
        }
    }

    fn flush(&mut self, ctx: &mut impl LowerCtx) -> Result<(), LowerError> {
        match self.pending.take() {
            Some(pending) => self.emit(ctx, pending),
            None => Ok(()),
        }
    }

    fn finalize(&mut self, ctx: &mut impl LowerCtx) -> Result<(), LowerError> {
        for patch in self.patches.drain(..) {
            let word = match &patch.inst {
                IrInst::BrIf { block_else, .. } => {
                    let target = ctx.resolve_block(*block_else)
                        .expect("finalize: unresolved block");
                    let disp = (target as i32 - patch.offset as i32) / 4;
                    BCond {
                        cond: patch.cond.unwrap(),
                        offset: disp,
                    }
                    .encode_word()
                }
                IrInst::Call { func_idx } => {
                    let target = ctx.resolve_func(*func_idx)
                        .expect("finalize: unresolved function");
                    let disp = (target as i32 - patch.offset as i32) / 4;
                    Bl { offset: disp }.encode_word()
                }
                _ => unreachable!("unexpected patch instruction: {}", patch.inst),
            };
            ctx.patch_code(patch.offset, &word.to_le_bytes());
        }
        Ok(())
    }
}

impl Aarch64Backend {
    fn fuse(
        &mut self,
        ctx: &mut impl LowerCtx,
        pending: Operation,
        inst: IrInst,
        dbg_group_idx: usize,
    ) -> Result<(), LowerError> {
        match (&pending.op, &inst) {
            // Comp + BrIf → subs + b.cond (fused compare-and-branch)
            (
                CompoundOperation::Base(IrInst::Alu {
                    op: AluOp::Comp(c),
                    dst,
                    lhs,
                    rhs,
                }),
                IrInst::BrIf { .. },
            ) => {
                // subs goes under the Comp's group.
                autosynth_lower::dbg(|dbg| dbg.set_current_group(pending.dbg_group_idx));
                let (lhs_preg, _) = ctx.into_preg(&lhs, self);
                let (dst_preg, w) = ctx.define_register(&dst, self);
                lower_cmp(ctx, *c, dst_preg, lhs_preg, w, rhs, self)?;
                // b.cond goes under the BrIf's group.
                autosynth_lower::dbg(|dbg| dbg.set_current_group(dbg_group_idx));
                let cond = comp_op_to_cond(*c).invert();
                let offset = emit_inst_at(ctx, BCond { cond, offset: 0 })?;
                self.patches.push(Patch {
                    offset,
                    inst: inst.clone(),
                    cond: Some(cond),
                });
                Ok(())
            }

            // No fusion possible — emit pending, store new inst.
            _ => {
                self.emit(ctx, pending)?;
                self.pending = Some(Operation {
                    dbg_group_idx,
                    op: CompoundOperation::Base(inst),
                });
                Ok(())
            }
        }
    }

    fn emit_base(&mut self, ctx: &mut impl LowerCtx, inst: IrInst) -> Result<(), LowerError> {
        match inst {
            IrInst::Alu { op, dst, lhs, rhs } => lower_alu(self, ctx, op, dst, lhs, rhs),
            IrInst::Load { dst, base, offset } => lower_load(self, ctx, dst, base, offset),
            IrInst::Store { src, base, offset } => lower_store(self, ctx, src, base, offset),
            IrInst::Move { dst, src } => lower_move(self, ctx, dst, src),
            IrInst::Return => {
                use autosynth_isa_aarch64::Ret;
                emit_inst(
                    ctx,
                    Ret {
                        rn: XGpr(GprId::from_index(30)),
                    },
                )
            }
            IrInst::Call { func_idx } => lower_call(self, ctx, func_idx),
            other => {
                unreachable!("backend received unexpected instruction: {other}")
            }
        }
    }

    fn emit(&mut self, ctx: &mut impl LowerCtx, pending: Operation) -> Result<(), LowerError> {
        let group = pending.dbg_group_idx;
        autosynth_lower::dbg(|dbg| dbg.set_current_group(group));
        match pending.op {
            CompoundOperation::Base(inst) => self.emit_base(ctx, inst),
        }
    }
}

/// Map a [`CompOp`] to the ARM64 condition code for branching.
///
/// Used by the orchestrator after emitting a comparison instruction
/// to determine the correct `b.cond` for the subsequent [`IrInst::BrIf`].
pub fn comp_op_to_cond(op: CompOp) -> Cond {
    match op {
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
    }
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Encode and emit a single machine instruction.
///
/// Pushes the encoded bytes into the code buffer via `ctx.emit_code()`
/// and annotates the thread-local debugger.
#[inline]
/// Encode and emit a single machine instruction.
fn emit_inst(
    ctx: &mut impl LowerCtx,
    inst: impl Aarch64Inst + core::fmt::Display,
) -> Result<(), LowerError> {
    emit_inst_at(ctx, inst).map(|_| ())
}

/// Encode and emit a single machine instruction, returning the byte
/// offset where it was placed. Used for instructions that need patching.
fn emit_inst_at(
    ctx: &mut impl LowerCtx,
    inst: impl Aarch64Inst + core::fmt::Display,
) -> Result<usize, LowerError> {
    autosynth_lower::dbg(|dbg| {
        dbg.emit_machine_inst();
        dbg.set_machine("asm", &format!("{inst}"));
    });
    let word = inst.encode_word();
    Ok(ctx.emit_code(&word.to_le_bytes()))
}

fn to_wgpr(p: PReg) -> WGpr {
    WGpr(GprId::from_index(p.0))
}

fn to_xgpr(p: PReg) -> XGpr {
    XGpr(GprId::from_index(p.0))
}

/// Convert a physical register + width to a `GprOrZr` with the correct
/// w-reg (32-bit) or x-reg (64-bit) form.
fn to_gpr_or_zr(p: PReg, w: Width) -> GprOrZr {
    match w {
        Width::W32 => GprOrZr::from(to_wgpr(p)),
        Width::W64 => GprOrZr::from(to_xgpr(p)),
    }
}

/// Convert a physical register + width to a `GprOrSp` with the correct
/// w-reg (32-bit) or x-reg (64-bit) form.
fn to_gpr_or_sp(p: PReg, w: Width) -> GprOrSp {
    match w {
        Width::W32 => GprOrSp::from(to_wgpr(p)),
        Width::W64 => GprOrSp::from(Gpr::X(to_xgpr(p))),
    }
}

/// Scale a byte offset by register width, returning a UImm12 for
/// unsigned-offset load/store encoding.
///
/// ARM64 scaled addressing requires the byte offset to be a multiple
/// of the access width (4 for W32, 8 for W64). Misaligned offsets are
/// a bug in the IR — we return an error rather than silently truncating.
fn scale_offset(offset: u32, w: Width) -> Result<UImm12, LowerError> {
    let size = w.bytes();
    if offset % size != 0 {
        return Err(LowerError::MisalignedOffset);
    }
    UImm12::try_from((offset / size) as i64).map_err(|_| LowerError::ImmediateOutOfRange)
}

fn lower_move(
    backend: &mut Aarch64Backend,
    ctx: &mut impl LowerCtx,
    dst: Register,
    src: Register,
) -> Result<(), LowerError> {
    let (dst_preg, w) = ctx.define_register(&dst, backend);
    let (src_preg, _) = ctx.resolve_register(&src, backend);
    let rd = to_gpr_or_zr(dst_preg, w);
    let rn = to_gpr_or_zr(src_preg, w);
    let zr = match w {
        Width::W32 => GprOrZr::Wzr,
        Width::W64 => GprOrZr::Xzr,
    };
    use autosynth_isa_aarch64::OrrReg;
    emit_inst(ctx, OrrReg { rd, rn: zr, rm: rn })
}

fn lower_load(
    backend: &mut Aarch64Backend,
    ctx: &mut impl LowerCtx,
    dst: Register,
    base: PReg,
    offset: u32,
) -> Result<(), LowerError> {
    let (dst_preg, w) = ctx.define_register(&dst, backend);
    let imm = scale_offset(offset, w)?;
    let rt = to_gpr_or_zr(dst_preg, w);
    let rn = GprOrSp::from(Gpr::X(to_xgpr(base)));
    emit_inst(
        ctx,
        LdrUoff {
            rt,
            rn,
            offset: imm,
        },
    )
}

fn lower_store(
    backend: &mut Aarch64Backend,
    ctx: &mut impl LowerCtx,
    src: Operand,
    base: PReg,
    offset: u32,
) -> Result<(), LowerError> {
    let (src_preg, w) = ctx.into_preg(&src, backend);
    let imm = scale_offset(offset, w)?;
    let rt = to_gpr_or_zr(src_preg, w);
    let rn = GprOrSp::from(Gpr::X(to_xgpr(base)));
    emit_inst(
        ctx,
        StrUoff {
            rt,
            rn,
            offset: imm,
        },
    )
}

fn lower_alu(
    backend: &mut Aarch64Backend,
    ctx: &mut impl LowerCtx,
    op: AluOp,
    dst: Register,
    lhs: Operand,
    rhs: Operand,
) -> Result<(), LowerError> {
    let (lhs_preg, _) = ctx.into_preg(&lhs, backend);
    let (dst_preg, w) = ctx.define_register(&dst, backend);

    match op {
        AluOp::Comp(c) => lower_cmp(ctx, c, dst_preg, lhs_preg, w, &rhs, backend),
        AluOp::Add => lower_add(ctx, dst_preg, lhs_preg, w, &rhs, backend),
        AluOp::Sub => lower_sub(ctx, dst_preg, lhs_preg, w, &rhs, backend),
        AluOp::Mul => todo!("mul not yet in ISA crate"),
        AluOp::And => todo!("and not yet in ISA crate"),
        AluOp::Or => todo!("or not yet in ISA crate"),
        AluOp::Xor => todo!("xor not yet in ISA crate"),
        AluOp::Shl => todo!("shl not yet in ISA crate"),
        AluOp::ShrS => todo!("shr_s not yet in ISA crate"),
        AluOp::ShrU => todo!("shr_u not yet in ISA crate"),
    }
}

fn lower_call(
    backend: &mut Aarch64Backend,
    ctx: &mut impl LowerCtx,
    func_idx: FunctionIdx,
) -> Result<(), LowerError> {
    let offset = emit_inst_at(ctx, Bl { offset: 0 })?;
    backend.patches.push(Patch {
        offset,
        inst: IrInst::Call { func_idx },
        cond: None,
    });
    Ok(())
}

fn lower_cmp(
    ctx: &mut impl LowerCtx,
    _op: CompOp,
    dst: PReg,
    lhs: PReg,
    w: Width,
    rhs: &Operand,
    backend: &mut Aarch64Backend,
) -> Result<(), LowerError> {
    let rd = to_gpr_or_zr(dst, w);
    match ctx.try_imm_or_preg::<UImm12>(rhs, backend) {
        PRegOr::Imm(imm) => {
            let rn = to_gpr_or_sp(lhs, w);
            emit_inst(ctx, SubsImm { rd, rn, imm })
        }
        PRegOr::PReg(rhs_preg) => {
            let rn = to_gpr_or_zr(lhs, w);
            let rm = to_gpr_or_zr(rhs_preg, w);
            emit_inst(ctx, SubsReg { rd, rn, rm })
        }
    }
}

fn lower_add(
    ctx: &mut impl LowerCtx,
    dst: PReg,
    lhs: PReg,
    w: Width,
    rhs: &Operand,
    backend: &mut Aarch64Backend,
) -> Result<(), LowerError> {
    match ctx.try_imm_or_preg::<UImm12>(rhs, backend) {
        PRegOr::Imm(imm) => {
            let rd = to_gpr_or_sp(dst, w);
            let rn = to_gpr_or_sp(lhs, w);
            emit_inst(ctx, AddImm { rd, rn, imm })
        }
        PRegOr::PReg(rhs_preg) => {
            let rd = to_gpr_or_zr(dst, w);
            let rn = to_gpr_or_zr(lhs, w);
            let rm = to_gpr_or_zr(rhs_preg, w);
            emit_inst(ctx, AddReg { rd, rn, rm })
        }
    }
}

fn lower_sub(
    ctx: &mut impl LowerCtx,
    dst: PReg,
    lhs: PReg,
    w: Width,
    rhs: &Operand,
    backend: &mut Aarch64Backend,
) -> Result<(), LowerError> {
    match ctx.try_imm_or_preg::<UImm12>(rhs, backend) {
        PRegOr::Imm(imm) => {
            let rd = to_gpr_or_sp(dst, w);
            let rn = to_gpr_or_sp(lhs, w);
            emit_inst(ctx, SubImm { rd, rn, imm })
        }
        PRegOr::PReg(rhs_preg) => {
            let rd = to_gpr_or_zr(dst, w);
            let rn = to_gpr_or_zr(lhs, w);
            let rm = to_gpr_or_zr(rhs_preg, w);
            emit_inst(ctx, SubReg { rd, rn, rm })
        }
    }
}
