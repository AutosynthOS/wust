/// AArch64 machine code emitter.
///
/// Encodes fully-resolved VCode instructions to ARM64 machine code.
/// All operands must be concrete — PRegs and immediates only.
///
/// Branch/jump instructions are emitted with placeholder offsets.
/// `finalize()` resolves all patch sites using label positions from
/// the CodeContext, re-encoding each instruction with the real
/// displacement.
use autosynth_emitter::{CodeContext, EmitError, Emitter};
use autosynth_ir::{AluOp, BlockId, CodeCtx, CodeCtxUnzipper, CompOp, Label, Operand, VCode};
use autosynth_isa::{PReg, SImm19, SImm26, Width};
use autosynth_isa::{UImm16};
use autosynth_isa_aarch64::{
    Aarch64Inst, AddImm, AddReg, B, BCond, Cond, Movk, Movz, Ret, SubsImm, SubsReg,
    reg::{Gpr, GprId, GprOrSp, GprOrZr, WGpr, XGpr},
};

struct PatchSite {
    offset: usize,
    target: Label,
    kind: PatchKind,
}

enum PatchKind {
    B,
    BCond(Cond),
}

pub struct Aarch64Emitter {
    func_idx: autosynth_ir::FunctionIdx,
    patches: Vec<PatchSite>,
}

impl Aarch64Emitter {
    pub fn new(func_idx: autosynth_ir::FunctionIdx) -> Self {
        Self {
            func_idx,
            patches: Vec::new(),
        }
    }

    pub fn finalize(&mut self, ctx: &mut impl CodeContext) -> Result<(), EmitError> {
        for patch in self.patches.drain(..) {
            let target_offset = ctx.label_offset(patch.target)
                .ok_or(EmitError::UnresolvedLabel)?;
            let word_displacement = (target_offset as i64 - patch.offset as i64) / 4;

            let word = match patch.kind {
                PatchKind::B => {
                    let offset = SImm26::try_from(word_displacement as i32)
                        .map_err(|_| EmitError::ImmediateOutOfRange)?;
                    B { offset }.encode_word()
                }
                PatchKind::BCond(cond) => {
                    let offset = SImm19::try_from(word_displacement as i32)
                        .map_err(|_| EmitError::ImmediateOutOfRange)?;
                    BCond { cond, offset }.encode_word()
                }
            };
            ctx.write_bytes(patch.offset, &word.to_le_bytes())
                .map_err(|_| EmitError::ImmediateOutOfRange)?;
        }
        Ok(())
    }
}

impl Emitter for Aarch64Emitter {
    fn emit(
        &mut self,
        stream: &mut CodeCtx,
        ctx: &mut impl CodeContext,
    ) -> Result<(), EmitError> {
        let owned = CodeCtx { stream: core::mem::take(&mut stream.stream) };
        let mut uz = owned.unzip();

        while let Some(inst) = uz.next_inst() {
            match inst {
                VCode::Alu { ref op } => emit_alu(op, &mut uz, ctx)?,
                VCode::BrIf { ref op, block_if, block_else } => {
                    emit_brif(self, op, block_if, block_else, &mut uz, ctx)?;
                }
                VCode::Branch { target } => emit_branch(self, target, ctx)?,
                VCode::Materialize => emit_materialize(&mut uz, ctx)?,
                VCode::Return => encode(Ret { rn: XGpr(GprId::LINK_REGISTER) }, ctx)?,
                _ => return Err(EmitError::Unhandled),
            }
        }
        Ok(())
    }
}

fn next_op(uz: &mut CodeCtxUnzipper) -> Result<Operand, EmitError> {
    uz.next_operand().map_err(|_| EmitError::OperandUnderflow)
}

fn next_dst(uz: &mut CodeCtxUnzipper) -> Result<(PReg, Width), EmitError> {
    match uz.next_operand() {
        Ok(Operand::DstPReg(preg, width)) => Ok((preg, width)),
        _ => Err(EmitError::OperandUnderflow),
    }
}

fn emit_alu(
    op: &AluOp,
    uz: &mut CodeCtxUnzipper,
    ctx: &mut impl CodeContext,
) -> Result<(), EmitError> {
    let lhs = next_op(uz)?;
    let rhs = next_op(uz)?;
    let (dst, width) = next_dst(uz)?;

    match op {
        AluOp::Add => {
            let lhs_preg = expect_preg(&lhs)?;

            match rhs {
                Operand::UImm12(imm) => {
                    let rd = to_gpr_or_sp(dst, width);
                    let rn = to_gpr_or_sp(lhs_preg, width);
                    encode(AddImm { rd, rn, imm }, ctx)
                }
                Operand::PReg(preg) => {
                    let rd = to_gpr_or_zr(dst, width);
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
    emitter: &mut Aarch64Emitter,
    op: &CompOp,
    _block_if: BlockId,
    block_else: BlockId,
    uz: &mut CodeCtxUnzipper,
    ctx: &mut impl CodeContext,
) -> Result<(), EmitError> {
    let lhs = next_op(uz)?;
    let rhs = next_op(uz)?;

    let lhs_preg = expect_preg(&lhs)?;
    let width = Width::W32;

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

    let cond = comp_op_to_cond(op).invert();
    let patch_offset = ctx.offset();
    encode(BCond { cond, offset: SImm19::try_from(0).unwrap() }, ctx)?;
    emitter.patches.push(PatchSite {
        offset: patch_offset,
        target: Label::Block(emitter.func_idx, block_else),
        kind: PatchKind::BCond(cond),
    });

    Ok(())
}

fn emit_branch(
    emitter: &mut Aarch64Emitter,
    target: BlockId,
    ctx: &mut impl CodeContext,
) -> Result<(), EmitError> {
    let patch_offset = ctx.offset();
    encode(B { offset: SImm26::try_from(0).unwrap() }, ctx)?;
    emitter.patches.push(PatchSite {
        offset: patch_offset,
        target: Label::Block(emitter.func_idx, target),
        kind: PatchKind::B,
    });
    Ok(())
}

fn emit_materialize(
    uz: &mut CodeCtxUnzipper,
    ctx: &mut impl CodeContext,
) -> Result<(), EmitError> {
    let val = next_op(uz)?;
    let (dst_preg, width) = next_dst(uz)?;

    let Operand::Const(imm) = val else {
        return Err(EmitError::UnresolvedOperand);
    };

    let rd = to_gpr_or_zr(dst_preg, width);
    let uval = imm as u64;
    let n = match width { Width::W32 => 2, Width::W64 => 4 };
    let chunk = |hw: usize| UImm16::from(((uval >> (hw * 16)) & 0xFFFF) as u16);

    encode(Movz { rd, imm: chunk(0), hw: 0 }, ctx)?;
    for hw in 1..n {
        let imm = chunk(hw);
        if imm.value() != 0 {
            encode(Movk { rd, imm, hw: hw as u8 }, ctx)?;
        }
    }

    Ok(())
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
