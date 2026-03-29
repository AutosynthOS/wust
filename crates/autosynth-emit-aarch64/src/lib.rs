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
use autosynth_ir::{AluOp, BlockId, CodeCtx, CompOp, Label, Operand, VCode};
use autosynth_isa::{PReg, SImm19, SImm26, Width};
use autosynth_isa_aarch64::{
    Aarch64Inst, AddImm, AddReg, B, BCond, Cond, Ret, SubsImm, SubsReg,
    reg::{Gpr, GprId, GprOrSp, GprOrZr, WGpr, XGpr},
};

/// A recorded patch site — an instruction that needs its offset
/// resolved after all labels are known.
struct PatchSite {
    /// Byte offset of the instruction in the code buffer.
    offset: usize,
    /// The target label to resolve.
    target: Label,
    /// What kind of instruction to re-encode.
    kind: PatchKind,
}

enum PatchKind {
    /// B (unconditional branch) — SImm26 word offset.
    B,
    /// B.cond (conditional branch) — SImm19 word offset.
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

    /// Resolve all recorded patch sites.
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
        while let Some(item) = stream.next() {
            match item {
                VCode::Operand(_) => {
                    // Stray operand — shouldn't happen in a well-formed stream.
                    return Err(EmitError::UnresolvedOperand);
                }
                VCode::Alu { ref op } => emit_alu(op, stream, ctx)?,
                VCode::BrIf { ref op, block_if, block_else } => {
                    emit_brif(self, op, block_if, block_else, stream, ctx)?;
                }
                VCode::Branch { target } => emit_branch(self, target, ctx)?,
                VCode::Materialize => emit_materialize(stream, ctx)?,
                VCode::Return => encode(Ret { rn: XGpr(GprId::LINK_REGISTER) }, ctx)?,
                _ => return Err(EmitError::Unhandled),
            }
        }
        Ok(())
    }
}

fn next_op(stream: &mut CodeCtx) -> Result<Operand, EmitError> {
    stream.next_operand().map_err(|_| EmitError::OperandUnderflow)
}

fn emit_alu(
    op: &AluOp,
    stream: &mut CodeCtx,
    ctx: &mut impl CodeContext,
) -> Result<(), EmitError> {
    let lhs = next_op(stream)?;
    let rhs = next_op(stream)?;
    let dst = next_op(stream)?;

    match op {
        AluOp::Add => {
            let dst_preg = expect_preg(&dst)?;
            let lhs_preg = expect_preg(&lhs)?;
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
    emitter: &mut Aarch64Emitter,
    op: &CompOp,
    block_if: BlockId,
    block_else: BlockId,
    stream: &mut CodeCtx,
    ctx: &mut impl CodeContext,
) -> Result<(), EmitError> {
    let lhs = next_op(stream)?;
    let rhs = next_op(stream)?;

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
    stream: &mut CodeCtx,
    ctx: &mut impl CodeContext,
) -> Result<(), EmitError> {
    let val = next_op(stream)?;
    let dst = next_op(stream)?;

    let Operand::Const(imm) = val else {
        return Err(EmitError::UnresolvedOperand);
    };
    let dst_preg = expect_preg(&dst)?;

    // TODO: proper movz/movk sequence for large constants.
    // For now, encode as movz (16-bit immediate, zero-extend).
    let word = 0x52800000 | ((imm as u32 & 0xFFFF) << 5) | (dst_preg.0 as u32);
    ctx.emit_bytes(&word.to_le_bytes()).map_err(|_| EmitError::ImmediateOutOfRange)
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
