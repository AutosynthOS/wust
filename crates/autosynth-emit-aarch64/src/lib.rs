/// AArch64 machine code emitter.
///
/// Encodes fully-resolved VCode instructions to ARM64 machine code.
/// All operands must be concrete — PRegs and immediates only.
use autosynth_emitter::{CodeContext, EmitError, Emitter};
use autosynth_ir::{AluOp, CompOp, Operand, VCode};
use autosynth_isa::{PReg, SImm19, SImm26, Width};
use autosynth_isa_aarch64::{
    Aarch64Inst, AddImm, AddReg, B, BCond, Cond, Ret, SubsImm, SubsReg,
    reg::{Gpr, GprId, GprOrSp, GprOrZr, WGpr, XGpr},
};

pub struct Aarch64Emitter;

impl Aarch64Emitter {
    pub fn new() -> Self {
        Self
    }
}

impl Emitter for Aarch64Emitter {
    fn emit(
        &mut self,
        inst: &VCode,
        operands: &mut impl Iterator<Item = Operand>,
        ctx: &mut impl CodeContext,
    ) -> Result<(), EmitError> {
        match inst {
            VCode::Alu { op } => emit_alu(op, operands, ctx),
            VCode::BrIf { op, .. } => emit_brif(op, operands, ctx),
            VCode::Branch { .. } => encode(B { offset: SImm26::try_from(0x1FFFFFF).unwrap() }, ctx),
            VCode::Return => encode(Ret { rn: XGpr(GprId::LINK_REGISTER) }, ctx),
            _ => Err(EmitError::Unhandled),
        }
    }
}

fn next_op(operands: &mut impl Iterator<Item = Operand>) -> Result<Operand, EmitError> {
    operands.next().ok_or(EmitError::OperandUnderflow)
}

fn emit_alu(
    op: &AluOp,
    operands: &mut impl Iterator<Item = Operand>,
    ctx: &mut impl CodeContext,
) -> Result<(), EmitError> {
    let lhs = next_op(operands)?;
    let rhs = next_op(operands)?;
    let dst = next_op(operands)?;

    match op {
        AluOp::Add => {
            let dst_preg = expect_preg(&dst)?;
            let lhs_preg = expect_preg(&lhs)?;
            // Default to W32 — the emitter operates on fully-resolved
            // operands where width comes from instruction context.
            let width = Width::W32;

            match rhs {
                Operand::UImm12(imm) => {
                    let rd = to_gpr_or_sp(dst_preg, width);
                    let rn = to_gpr_or_sp(lhs_preg, width);
                    encode(AddImm { rd, rn, imm }, ctx)
                }
                Operand::PReg(preg) => {
                    let rd = to_gpr_or_zr(dst_preg, width);
                    let rn = to_gpr_or_zr(lhs_preg, width);
                    let rm = to_gpr_or_zr(preg, width);
                    encode(AddReg { rd, rn, rm }, ctx)
                }
                _ => Err(EmitError::UnresolvedOperand),
            }
        }
        _ => todo!("emit_alu: {op:?}"),
    }
}

fn emit_brif(
    op: &CompOp,
    operands: &mut impl Iterator<Item = Operand>,
    ctx: &mut impl CodeContext,
) -> Result<(), EmitError> {
    let lhs = next_op(operands)?;
    let rhs = next_op(operands)?;

    let lhs_preg = expect_preg(&lhs)?;
    let width = Width::W32;

    // Emit subs (flag-setting compare).
    match rhs {
        Operand::UImm12(imm) => {
            let rd = to_gpr_or_zr(lhs_preg, width);
            let rn = to_gpr_or_sp(lhs_preg, width);
            encode(SubsImm { rd, rn, imm }, ctx)?;
        }
        Operand::PReg(preg) => {
            let rd = to_gpr_or_zr(lhs_preg, width);
            let rn = to_gpr_or_zr(lhs_preg, width);
            let rm = to_gpr_or_zr(preg, width);
            encode(SubsReg { rd, rn, rm }, ctx)?;
        }
        _ => return Err(EmitError::UnresolvedOperand),
    }

    // Emit b.cond with placeholder max offset.
    // Inverted condition: BrIf branches to block_else when condition is FALSE.
    let cond = comp_op_to_cond(op).invert();
    encode(BCond { cond, offset: SImm19::try_from(0x3FFFF).unwrap() }, ctx)
}

fn comp_op_to_cond(op: &CompOp) -> Cond {
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

fn expect_preg(op: &Operand) -> Result<PReg, EmitError> {
    match op {
        Operand::PReg(preg) => Ok(*preg),
        _ => Err(EmitError::UnresolvedOperand),
    }
}

fn encode(inst: impl Aarch64Inst, ctx: &mut impl CodeContext) -> Result<(), EmitError> {
    let word = inst.encode_word();
    ctx.emit_bytes(&word.to_le_bytes()).map_err(|_| EmitError::ImmediateOutOfRange)
}

fn to_wgpr(p: PReg) -> WGpr { WGpr(GprId::from_index(p.0)) }
fn to_xgpr(p: PReg) -> XGpr { XGpr(GprId::from_index(p.0)) }

fn to_gpr_or_zr(p: PReg, w: Width) -> GprOrZr {
    match w {
        Width::W32 => GprOrZr::from(to_wgpr(p)),
        Width::W64 => GprOrZr::from(to_xgpr(p)),
    }
}

fn to_gpr_or_sp(p: PReg, w: Width) -> GprOrSp {
    if p.0 == GprOrSp::STACK_POINTER_IDX {
        return GprOrSp::Sp;
    }
    match w {
        Width::W32 => GprOrSp::from(to_wgpr(p)),
        Width::W64 => GprOrSp::from(Gpr::X(to_xgpr(p))),
    }
}
