//! AArch64 backend — pure instruction selection for ARM64.
//!
//! This crate translates IR operations into AArch64 machine code.
//! It does NOT manage register allocation, spilling, or materialization.
//! All operand resolution goes through [`autosynth_lower::LowerCtx`].

use autosynth_backend::{BackendEmitter, MachineConfig};
use autosynth_ir::{AluOp, CompOp, IrInst, Operand, Register};
use autosynth_isa::{PReg, PRegOr, UImm12, Width};
use autosynth_isa_aarch64::{
    Aarch64Inst, AddImm, AddReg, Cond, LdrUoff, StrUoff, SubImm, SubReg, SubsImm, SubsReg,
    reg::{Gpr, GprId, GprOrSp, GprOrZr, WGpr, XGpr},
};
use autosynth_lower::{self, LowerCtx};
use smallvec::SmallVec;

/// AArch64 backend. Never constructed — used only for the trait impl.
pub struct Aarch64Backend;

impl BackendEmitter for Aarch64Backend {
    fn machine_config() -> MachineConfig {
        let pool = (0u8..=30).filter(|&r| r != 18).map(PReg).collect();
        MachineConfig::new(pool)
    }

    fn emit(ctx: &mut impl LowerCtx, inst: IrInst) -> Result<SmallVec<[u8; 8]>, String> {
        let word = match inst {
            IrInst::Alu { op, dst, lhs, rhs } => lower_alu(ctx, op, dst, lhs, rhs)?,
            IrInst::Load { dst, base, offset } => lower_load(ctx, dst, base, offset)?,
            IrInst::Store { src, base, offset } => lower_store(ctx, src, base, offset)?,
            IrInst::BrIf { .. } => todo!("BrIf: orchestrator-driven"),
            IrInst::Branch { .. } => todo!("Branch: orchestrator-driven"),
            IrInst::Call { .. } => todo!("Call: orchestrator-driven"),
            IrInst::Return { .. } => todo!("Return: orchestrator-driven"),
        };
        Ok(SmallVec::from_slice(&word.to_le_bytes()))
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
fn scale_offset(offset: u32, w: Width) -> Result<UImm12, String> {
    let size = w.bytes();
    if offset % size != 0 {
        return Err(format!(
            "offset {offset} not aligned to {w} ({size}-byte) boundary"
        ));
    }
    UImm12::try_from((offset / size) as i64).map_err(|_| {
        format!(
            "offset {offset} out of range (scaled {}, max 4095)",
            offset / size
        )
    })
}

fn lower_load(
    ctx: &mut impl LowerCtx,
    dst: Register,
    base: PReg,
    offset: u32,
) -> Result<u32, String> {
    let (dst_preg, w) = autosynth_lower::define_register(&dst, ctx);
    let imm = scale_offset(offset, w)?;
    let rt = to_gpr_or_zr(dst_preg, w);
    let rn = GprOrSp::from(Gpr::X(to_xgpr(base)));
    Ok(LdrUoff { rt, rn, offset: imm }.encode_word())
}

fn lower_store(
    ctx: &mut impl LowerCtx,
    src: Operand,
    base: PReg,
    offset: u32,
) -> Result<u32, String> {
    let (src_preg, w) = autosynth_lower::into_preg(&src, ctx);
    let imm = scale_offset(offset, w)?;
    let rt = to_gpr_or_zr(src_preg, w);
    let rn = GprOrSp::from(Gpr::X(to_xgpr(base)));
    Ok(StrUoff { rt, rn, offset: imm }.encode_word())
}

fn lower_alu(
    ctx: &mut impl LowerCtx,
    op: AluOp,
    dst: Register,
    lhs: Operand,
    rhs: Operand,
) -> Result<u32, String> {
    let (dst_preg, w) = autosynth_lower::define_register(&dst, ctx);
    let (lhs_preg, _) = autosynth_lower::into_preg(&lhs, ctx);

    match op {
        AluOp::Comp(c) => lower_cmp(ctx, c, dst_preg, lhs_preg, w, &rhs),
        AluOp::Add => emit_add(ctx, dst_preg, lhs_preg, w, &rhs),
        AluOp::Sub => emit_sub(ctx, dst_preg, lhs_preg, w, &rhs),
        AluOp::Mul => todo!("mul not yet in ISA crate"),
        AluOp::And => todo!("and not yet in ISA crate"),
        AluOp::Or => todo!("or not yet in ISA crate"),
        AluOp::Xor => todo!("xor not yet in ISA crate"),
        AluOp::Shl => todo!("shl not yet in ISA crate"),
        AluOp::ShrS => todo!("shr_s not yet in ISA crate"),
        AluOp::ShrU => todo!("shr_u not yet in ISA crate"),
    }
}

fn lower_cmp(
    ctx: &mut impl LowerCtx,
    _op: CompOp,
    dst: PReg,
    lhs: PReg,
    w: Width,
    rhs: &Operand,
) -> Result<u32, String> {
    let rd = to_gpr_or_zr(dst, w);

    Ok(match autosynth_lower::try_imm_or_preg::<UImm12>(rhs, ctx) {
        PRegOr::Imm(imm) => {
            let rn = to_gpr_or_sp(lhs, w);
            SubsImm { rd, rn, imm }.encode_word()
        }
        PRegOr::PReg(rhs_preg) => {
            let rn = to_gpr_or_zr(lhs, w);
            let rm = to_gpr_or_zr(rhs_preg, w);
            SubsReg { rd, rn, rm }.encode_word()
        }
    })
}

fn emit_add(
    ctx: &mut impl LowerCtx,
    dst: PReg,
    lhs: PReg,
    w: Width,
    rhs: &Operand,
) -> Result<u32, String> {
    Ok(match autosynth_lower::try_imm_or_preg::<UImm12>(rhs, ctx) {
        PRegOr::Imm(imm) => {
            let rd = to_gpr_or_sp(dst, w);
            let rn = to_gpr_or_sp(lhs, w);
            AddImm { rd, rn, imm }.encode_word()
        }
        PRegOr::PReg(rhs_preg) => {
            let rd = to_gpr_or_zr(dst, w);
            let rn = to_gpr_or_zr(lhs, w);
            let rm = to_gpr_or_zr(rhs_preg, w);
            AddReg { rd, rn, rm }.encode_word()
        }
    })
}

fn emit_sub(
    ctx: &mut impl LowerCtx,
    dst: PReg,
    lhs: PReg,
    w: Width,
    rhs: &Operand,
) -> Result<u32, String> {
    Ok(match autosynth_lower::try_imm_or_preg::<UImm12>(rhs, ctx) {
        PRegOr::Imm(imm) => {
            let rd = to_gpr_or_sp(dst, w);
            let rn = to_gpr_or_sp(lhs, w);
            SubImm { rd, rn, imm }.encode_word()
        }
        PRegOr::PReg(rhs_preg) => {
            let rd = to_gpr_or_zr(dst, w);
            let rn = to_gpr_or_zr(lhs, w);
            let rm = to_gpr_or_zr(rhs_preg, w);
            SubReg { rd, rn, rm }.encode_word()
        }
    })
}
