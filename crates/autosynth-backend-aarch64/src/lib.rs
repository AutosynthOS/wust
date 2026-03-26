//! AArch64 backend — pure instruction selection for ARM64.
//!
//! This crate translates IR operations into AArch64 machine code.
//! It does NOT manage register allocation, spilling, or materialization.
//! All operand resolution goes through [`autosynth_lower::LowerCtx`].

use std::collections::HashMap;

use autosynth_ir::{AluOp, BlockId, CompOp, FunctionIdx, IrInst, VReg};
use autosynth_isa::{IsaReg, PReg, PRegOr, SImm19, SImm26, UImm12, Width};
use autosynth_isa_aarch64::{
    Aarch64Inst, AddImm, AddReg, B, BCond, Bl, Cond, LdrUoff, Movk, Movz, StrUoff, SubImm,
    SubReg, SubsImm, SubsReg, UImm16,
    reg::{Gpr, GprId, GprOrSp, GprOrZr, WGpr, XGpr},
};
use autosynth_lower::{trace, trace_do, LowerCtx, LowerCtxExt};
use autosynth_lower::{BackendEmitter, LowerError, MachineConfig};

/// A saved patch point — the byte offset of an instruction that needs
/// its offset field rewritten after all blocks are laid out.
#[allow(dead_code)]
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
#[allow(dead_code)]
pub struct Aarch64Backend {
    /// Code buffer for the backend.
    code: Vec<u8>,

    /// Map of block labels to their byte offsets.
    labels: HashMap<BlockId, usize>,

    /// Pending operations that need to be emitted.
    pending: Option<Operation>,
    /// Branch/call instructions that need offset patching after layout.
    patches: Vec<Patch>,
}

/// A deferred operation with its saved group index for correct
/// ASM parent attribution through deferred/fused paths.
#[derive(Debug)]
struct Operation {
    /// The instruction group this operation belongs to — restored
    /// before emitting so ASM events carry the right parent.
    #[cfg(feature = "trace")]
    group: String,
    op: CompoundOperation,
}

#[derive(Debug)]
enum CompoundOperation {
    /// A single deferred instruction, waiting to see if the next instruction can fuse with it.
    Base(IrInst),
}

impl BackendEmitter for Aarch64Backend {
    fn new() -> Self {
        Self {
            code: Vec::new(),
            labels: HashMap::new(),
            pending: None,
            patches: Vec::new(),
        }
    }

    fn machine_config() -> MachineConfig {
        let pool = (0u8..=31).map(PReg).collect();
        let isa_regs = HashMap::from([
            (IsaReg::FramePointer, PReg(29)),
            (IsaReg::StackPointer, PReg(31)),
            (IsaReg::ReturnAddress, PReg(30)),
            (IsaReg::PlatformReserved, PReg(18)),
        ]);
        MachineConfig::new(pool, isa_regs, 16)
    }

    fn lower(
        &mut self,
        ctx: &mut impl LowerCtx,
        inst: IrInst,
        emit: autosynth_lower::Emit,
    ) -> Result<(), LowerError> {
        if emit == autosynth_lower::Emit::Immediate {
            self.flush(ctx)?;
            let op = Operation {
                #[cfg(feature = "trace")]
                group: autosynth_lower::current_group(),
                op: CompoundOperation::Base(inst),
            };
            return self.emit(ctx, op);
        }

        match self.pending.take() {
            None => {
                trace!({"type": "defer", "inst": format!("{inst}")});
                self.pending = Some(Operation {
                    #[cfg(feature = "trace")]
                    group: autosynth_lower::current_group(),
                    op: CompoundOperation::Base(inst),
                });
                Ok(())
            }
            Some(pending) => {
                trace!({"type": "fuse_attempt", "inst": format!("{inst}")});
                self.fuse(ctx, pending, inst)
            }
        }
    }

    fn flush(&mut self, ctx: &mut impl LowerCtx) -> Result<(), LowerError> {
        match self.pending.take() {
            Some(pending) => self.emit(ctx, pending),
            None => Ok(()),
        }
    }

    fn bind_label(&mut self, block: BlockId) {
        self.labels.insert(block, self.code.len());
    }

    fn finalize(&mut self, _ctx: &mut impl LowerCtx) -> Result<(), LowerError> {
        for patch in std::mem::take(&mut self.patches) {
            let disp = |target: usize| (target as i64 - patch.offset as i64) / 4;

            match (&patch.inst, patch.cond) {
                (IrInst::BrIf { block_else, .. }, Some(cond)) => {
                    let offset = SImm19::try_from(disp(self.labels[block_else]))
                        .map_err(|_| LowerError::ImmediateOutOfRange)?;
                    let word = BCond { cond, offset }.encode_word();
                    self.patch_code(patch.offset, &word.to_le_bytes());
                }
                (IrInst::Branch { target }, None) => {
                    let offset = SImm26::try_from(disp(self.labels[target]))
                        .map_err(|_| LowerError::ImmediateOutOfRange)?;
                    let word = B { offset }.encode_word();
                    self.patch_code(patch.offset, &word.to_le_bytes());
                }
                (IrInst::Call { func_idx }, None) => {
                    // TODO: cross-function call patching — for now,
                    // resolve_func returns 0 (self-recursive only).
                    let target = self.resolve_func(*func_idx).unwrap_or(0);
                    let offset = SImm26::try_from(disp(target))
                        .map_err(|_| LowerError::ImmediateOutOfRange)?;
                    let word = Bl { offset }.encode_word();
                    self.patch_code(patch.offset, &word.to_le_bytes());
                }
                _ => {}
            }
        }
        Ok(())
    }

    fn code(&self) -> &[u8] {
        &self.code
    }

    fn materialize_const(&mut self, preg: PReg, val: i64, width: Width) -> Result<(), LowerError> {
        let rd = to_gpr_or_zr(preg, width);
        let uval = val as u64;
        let max_hw: u8 = match width {
            Width::W32 => 1,
            Width::W64 => 3,
        };
        let chunk = |hw: u8| ((uval >> (hw as u32 * 16)) & 0xFFFF) as u16;

        // MOVZ: load lowest 16 bits, zero the rest.
        emit_inst(
            self,
            Movz {
                rd,
                imm: UImm16::from(chunk(0)),
                hw: 0,
            },
        )?;

        // MOVK: patch in each non-zero 16-bit chunk above.
        for hw in 1..=max_hw {
            let bits = chunk(hw);
            if bits != 0 {
                emit_inst(
                    self,
                    Movk {
                        rd,
                        imm: UImm16::from(bits),
                        hw,
                    },
                )?;
            }
        }
        Ok(())
    }
}

#[allow(dead_code)]
impl Aarch64Backend {
    fn emit_code(&mut self, bytes: &[u8]) -> usize {
        let offset = self.code.len();
        self.code.extend_from_slice(bytes);
        offset
    }

    fn patch_code(&mut self, offset: usize, bytes: &[u8]) {
        self.code[offset..offset + bytes.len()].copy_from_slice(bytes);
    }

    fn resolve_block(&self, block: BlockId) -> Option<usize> {
        self.labels.get(&block).copied()
    }

    fn resolve_func(&self, _func_idx: FunctionIdx) -> Option<usize> {
        Some(0)
    }

    fn fuse(
        &mut self,
        ctx: &mut impl LowerCtx,
        pending: Operation,
        inst: IrInst,
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
                IrInst::BrIf { cond: cond_vreg, .. },
            ) => {
                // subs goes under the Comp's group.
                trace_do! { autosynth_lower::restore_group(&pending.group); }
                lower_cmp(ctx, *c, *dst, *lhs, *rhs, self)?;
                // Consume the cond vreg's remaining use — only the flags
                // matter, but the register needs to be freed.
                let _ = ctx.resolve_vreg(*cond_vreg, self)?;
                // b.cond goes under the BrIf's group.
                trace_do! { autosynth_lower::restore_group(&autosynth_lower::current_group()); }
                let cond = comp_op_to_cond(*c).invert();
                let offset = emit_inst_at(self, BCond { cond, offset: SImm19::try_from(0).unwrap() })?;
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
                    #[cfg(feature = "trace")]
                    group: autosynth_lower::current_group(),
                    op: CompoundOperation::Base(inst),
                });
                Ok(())
            }
        }
    }

    fn emit_base(&mut self, ctx: &mut impl LowerCtx, inst: IrInst) -> Result<(), LowerError> {
        match inst {
            IrInst::Alu { op, dst, lhs, rhs } => lower_alu(self, ctx, op, dst, lhs, rhs),
            IrInst::Load {
                dst,
                width,
                base,
                offset,
            } => lower_load(self, dst, width, base, offset),
            IrInst::Store {
                src,
                width,
                base,
                offset,
            } => lower_store(self, src, width, base, offset),
            IrInst::Move {
                dst,
                dst_width,
                src,
                src_width,
            } => lower_move(self, dst, dst_width, src, src_width),
            IrInst::Return => {
                use autosynth_isa_aarch64::Ret;
                emit_inst(
                    self,
                    Ret {
                        rn: XGpr(GprId::LINK_REGISTER),
                    },
                )
            }
            IrInst::Call { func_idx } => lower_call(self, func_idx),
            IrInst::Branch { target } => {
                let offset = emit_inst_at(self, B { offset: SImm26::try_from(0).unwrap() })?;
                self.patches.push(Patch {
                    offset,
                    inst: IrInst::Branch { target },
                    cond: None,
                });
                Ok(())
            }
            IrInst::Skipped { .. } => Ok(()),
            other => {
                unreachable!("backend received unexpected instruction: {other}")
            }
        }
    }

    fn emit(&mut self, ctx: &mut impl LowerCtx, pending: Operation) -> Result<(), LowerError> {
        trace_do! { autosynth_lower::restore_group(&pending.group); }
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
    backend: &mut Aarch64Backend,
    inst: impl Aarch64Inst + core::fmt::Display,
) -> Result<(), LowerError> {
    emit_inst_at(backend, inst).map(|_| ())
}

/// Encode and emit a single machine instruction, returning the byte
/// offset where it was placed. Used for instructions that need patching.
fn emit_inst_at(
    backend: &mut Aarch64Backend,
    inst: impl Aarch64Inst + core::fmt::Display,
) -> Result<usize, LowerError> {
    trace!({
        "type": "asm",
        "addr": backend.code.len(),
        "text": format!("{inst}"),
        "parent": autosynth_lower::current_group()
    });
    let word = inst.encode_word();
    Ok(backend.emit_code(&word.to_le_bytes()))
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
    if p.0 == GprOrSp::STACK_POINTER_IDX {
        return GprOrSp::Sp;
    }
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
    dst: PReg,
    dst_width: Width,
    src: PReg,
    src_width: Width,
) -> Result<(), LowerError> {
    let rd = to_gpr_or_zr(dst, dst_width);
    let rn = to_gpr_or_zr(src, src_width);
    let zr = match dst_width {
        Width::W32 => GprOrZr::Wzr,
        Width::W64 => GprOrZr::Xzr,
    };
    use autosynth_isa_aarch64::OrrReg;
    emit_inst(backend, OrrReg { rd, rn: zr, rm: rn })
}

fn lower_load(
    backend: &mut Aarch64Backend,
    dst: PReg,
    width: Width,
    base: PReg,
    offset: u32,
) -> Result<(), LowerError> {
    let imm = scale_offset(offset, width)?;
    let rt = to_gpr_or_zr(dst, width);
    let rn = to_gpr_or_sp(base, Width::W64);
    emit_inst(
        backend,
        LdrUoff {
            rt,
            rn,
            offset: imm,
        },
    )
}

fn lower_store(
    backend: &mut Aarch64Backend,
    src: PReg,
    src_width: Width,
    base: PReg,
    offset: u32,
) -> Result<(), LowerError> {
    let imm = scale_offset(offset, src_width)?;
    let rt = to_gpr_or_zr(src, src_width);
    let rn = to_gpr_or_sp(base, Width::W64);
    emit_inst(
        backend,
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
    dst: VReg,
    lhs: VReg,
    rhs: VReg,
) -> Result<(), LowerError> {
    match op {
        AluOp::Comp(c) => lower_cmp(ctx, c, dst, lhs, rhs, backend),
        AluOp::Add => lower_add(ctx, dst, lhs, rhs, backend),
        AluOp::Sub => lower_sub(ctx, dst, lhs, rhs, backend),
        _ => todo!("{op:?} not yet in ISA crate"),
    }
}

fn lower_call(backend: &mut Aarch64Backend, func_idx: FunctionIdx) -> Result<(), LowerError> {
    let offset = emit_inst_at(backend, Bl { offset: SImm26::try_from(0).unwrap() })?;
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
    dst: VReg,
    lhs: VReg,
    rhs: VReg,
    backend: &mut Aarch64Backend,
) -> Result<(), LowerError> {
    let (lhs_preg, lhs_width) = ctx.into_preg(lhs, backend)?;
    let rhs_resolved = ctx.try_imm_or_preg::<UImm12>(rhs, backend)?;
    let (dst_preg, dst_width) = ctx.define_vreg(dst, backend)?;
    let rd = to_gpr_or_zr(dst_preg, dst_width);
    match rhs_resolved {
        PRegOr::Imm(imm) => {
            let rn = to_gpr_or_sp(lhs_preg, lhs_width);
            emit_inst(backend, SubsImm { rd, rn, imm })
        }
        PRegOr::PReg(rhs_preg, rhs_width) => {
            let rn = to_gpr_or_zr(lhs_preg, lhs_width);
            let rm = to_gpr_or_zr(rhs_preg, rhs_width);
            emit_inst(backend, SubsReg { rd, rn, rm })
        }
    }
}

fn lower_add(
    ctx: &mut impl LowerCtx,
    dst: VReg,
    lhs: VReg,
    rhs: VReg,
    backend: &mut Aarch64Backend,
) -> Result<(), LowerError> {
    let (lhs_preg, lhs_width) = ctx.into_preg(lhs, backend)?;
    let rhs_resolved = ctx.try_imm_or_preg::<UImm12>(rhs, backend)?;
    let (dst_preg, dst_width) = ctx.define_vreg(dst, backend)?;
    match rhs_resolved {
        PRegOr::Imm(imm) => {
            let rd = to_gpr_or_sp(dst_preg, dst_width);
            let rn = to_gpr_or_sp(lhs_preg, lhs_width);
            emit_inst(backend, AddImm { rd, rn, imm })
        }
        PRegOr::PReg(rhs_preg, width) => {
            let rd = to_gpr_or_zr(dst_preg, dst_width);
            let rn = to_gpr_or_zr(lhs_preg, lhs_width);
            let rm = to_gpr_or_zr(rhs_preg, width);
            emit_inst(backend, AddReg { rd, rn, rm })
        }
    }
}

fn lower_sub(
    ctx: &mut impl LowerCtx,
    dst: VReg,
    lhs: VReg,
    rhs: VReg,
    backend: &mut Aarch64Backend,
) -> Result<(), LowerError> {
    let (lhs_preg, lhs_width) = ctx.into_preg(lhs, backend)?;
    let rhs_resolved = ctx.try_imm_or_preg::<UImm12>(rhs, backend)?;
    let (dst_preg, dst_width) = ctx.define_vreg(dst, backend)?;
    match rhs_resolved {
        PRegOr::Imm(imm) => {
            let rd = to_gpr_or_sp(dst_preg, dst_width);
            let rn = to_gpr_or_sp(lhs_preg, lhs_width);
            emit_inst(backend, SubImm { rd, rn, imm })
        }
        PRegOr::PReg(rhs_preg, width) => {
            let rd = to_gpr_or_zr(dst_preg, dst_width);
            let rn = to_gpr_or_zr(lhs_preg, lhs_width);
            let rm = to_gpr_or_zr(rhs_preg, width);
            emit_inst(backend, SubReg { rd, rn, rm })
        }
    }
}
