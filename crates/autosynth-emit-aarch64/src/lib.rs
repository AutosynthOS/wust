/// AArch64 machine code emitter.
use autosynth_emitter::{CodeContext, Emitter};
use autosynth_ir::{AluOp, BlockId, CodeCtxUnzipper, CompOp, CompileError, Label, Operand, VCode};
use autosynth_isa::{PReg, SImm19, SImm26, UImm16, Width};
use autosynth_isa_aarch64::{
    Aarch64Inst, AddImm, AddReg, B, BCond, Bl as BlInst, Cond, Movk, Movz, Ret, SubsImm, SubsReg,
    reg::{Gpr, GprId, GprOrSp, GprOrZr, WGpr, XGpr},
};

struct PatchSite {
    offset: usize,
    target: Label,
    kind: PatchKind,
}

enum PatchKind {
    B,
    Bl,
    BCond(Cond),
}

pub struct Aarch64Emitter {
    func_idx: autosynth_ir::FunctionIdx,
    patches: Vec<PatchSite>,
}

impl Aarch64Emitter {
    pub fn new(func_idx: autosynth_ir::FunctionIdx) -> Self {
        Self { func_idx, patches: Vec::new() }
    }

    pub fn finalize(&mut self, ctx: &mut impl CodeContext) -> Result<(), CompileError> {
        for patch in self.patches.drain(..) {
            let target_offset = ctx.label_offset(patch.target)
                .ok_or(CompileError::UnresolvedLabel)?;
            let byte_disp = target_offset as isize - patch.offset as isize;
            let word_disp = byte_disp / 4;

            let word = match patch.kind {
                PatchKind::B => {
                    let offset = SImm26::try_from(word_disp)
                        .map_err(|_| CompileError::ImmediateOutOfRange)?;
                    B { offset }.encode_word()
                }
                PatchKind::Bl => {
                    let offset = SImm26::try_from(word_disp)
                        .map_err(|_| CompileError::ImmediateOutOfRange)?;
                    BlInst { offset }.encode_word()
                }
                PatchKind::BCond(cond) => {
                    let offset = SImm19::try_from(word_disp)
                        .map_err(|_| CompileError::ImmediateOutOfRange)?;
                    BCond { cond, offset }.encode_word()
                }
            };
            ctx.write_bytes(patch.offset, &word.to_le_bytes())
                .map_err(|_| CompileError::ImmediateOutOfRange)?;
        }
        Ok(())
    }
}

impl Emitter for Aarch64Emitter {
    fn emit(
        &mut self,
        mut uz: CodeCtxUnzipper,
        ctx: &mut impl CodeContext,
    ) -> Result<(), CompileError> {
        while let Some(inst) = uz.next_inst() {
            match inst {
                VCode::Alu { ref op } => emit_alu(op, &mut uz, ctx)?,
                VCode::BrIf { ref op, block_if: _, block_else } => {
                    emit_brif(self, op, block_else, &mut uz, ctx)?;
                }
                VCode::Branch { target } => emit_branch(self, target, ctx)?,
                VCode::Bl { target } => emit_bl(self, target, ctx)?,
                VCode::Materialize => emit_materialize(&mut uz, ctx)?,
                VCode::Return => encode(Ret { rn: XGpr(GprId::LINK_REGISTER) }, ctx)?,
                _ => return Err(CompileError::UnhandledInstruction),
            }
        }
        Ok(())
    }
}

fn emit_alu(
    op: &AluOp,
    uz: &mut CodeCtxUnzipper,
    ctx: &mut impl CodeContext,
) -> Result<(), CompileError> {
    let lhs = uz.next_preg()?;
    let rhs = uz.next_operand()?;
    let (dst, width) = uz.next_dst()?;

    match op {
        AluOp::Add => match rhs {
            Operand::UImm12(imm) => {
                encode(AddImm { rd: to_gpr_or_sp(dst, width), rn: to_gpr_or_sp(lhs, width), imm }, ctx)
            }
            Operand::PReg(rm) => {
                encode(AddReg { rd: to_gpr_or_zr(dst, width), rn: to_gpr_or_zr(lhs, width), rm: to_gpr_or_zr(rm, width) }, ctx)
            }
            _ => Err(CompileError::UnresolvedOperand),
        }
        _ => todo!("emit_alu: {op:?}"),
    }
}

fn emit_brif(
    emitter: &mut Aarch64Emitter,
    op: &CompOp,
    block_else: BlockId,
    uz: &mut CodeCtxUnzipper,
    ctx: &mut impl CodeContext,
) -> Result<(), CompileError> {
    let lhs = uz.next_preg()?;
    let rhs = uz.next_operand()?;
    let width = Width::W32; // TODO: derive from operand width

    match rhs {
        Operand::UImm12(imm) => {
            encode(SubsImm { rd: to_gpr_or_zr(lhs, width), rn: to_gpr_or_sp(lhs, width), imm }, ctx)?;
        }
        Operand::PReg(rm) => {
            encode(SubsReg { rd: to_gpr_or_zr(lhs, width), rn: to_gpr_or_zr(lhs, width), rm: to_gpr_or_zr(rm, width) }, ctx)?;
        }
        _ => return Err(CompileError::UnresolvedOperand),
    }

    let cond = comp_op_to_cond(op).invert();
    let patch_offset = ctx.offset();
    encode(BCond { cond, offset: SImm19::try_from(0isize).unwrap() }, ctx)?;
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
) -> Result<(), CompileError> {
    let patch_offset = ctx.offset();
    encode(B { offset: SImm26::try_from(0isize).unwrap() }, ctx)?;
    emitter.patches.push(PatchSite {
        offset: patch_offset,
        target: Label::Block(emitter.func_idx, target),
        kind: PatchKind::B,
    });
    Ok(())
}

fn emit_bl(
    emitter: &mut Aarch64Emitter,
    target: Label,
    ctx: &mut impl CodeContext,
) -> Result<(), CompileError> {
    let patch_offset = ctx.offset();
    encode(BlInst { offset: SImm26::try_from(0isize).unwrap() }, ctx)?;
    emitter.patches.push(PatchSite {
        offset: patch_offset,
        target,
        kind: PatchKind::Bl,
    });
    Ok(())
}

fn emit_materialize(
    uz: &mut CodeCtxUnzipper,
    ctx: &mut impl CodeContext,
) -> Result<(), CompileError> {
    let val = uz.next_operand()?;
    let (dst, width) = uz.next_dst()?;

    let Operand::Const(imm) = val else {
        return Err(CompileError::UnresolvedOperand);
    };

    let rd = to_gpr_or_zr(dst, width);
    let uval = imm as u64;
    let chunk = |hw: u8| UImm16::from(((uval >> (hw as u32 * 16)) & 0xFFFF) as u16);

    encode(Movz { rd, imm: chunk(0), hw: 0 }, ctx)?;
    for hw in 1..(width.bytes() / 2) as u8 {
        let imm = chunk(hw);
        if imm.value() != 0 {
            encode(Movk { rd, imm, hw }, ctx)?;
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

fn encode(inst: impl Aarch64Inst, ctx: &mut impl CodeContext) -> Result<(), CompileError> {
    ctx.emit_bytes(&inst.encode_word().to_le_bytes())
        .map_err(|_| CompileError::ImmediateOutOfRange)
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
    if p.0 == GprOrSp::STACK_POINTER_IDX { return GprOrSp::Sp; }
    match w {
        Width::W32 => GprOrSp::from(to_wgpr(p)),
        Width::W64 => GprOrSp::from(Gpr::X(to_xgpr(p))),
    }
}
