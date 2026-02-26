use crate::cfg::{self, CfgInfo};
use crate::context::JitContext;
use crate::emit::{Cond, Emitter, PatchPoint, Reg};
use crate::ir::{IrCond, IrFunction, IrInst, Label, VReg};
use crate::regalloc_adapter::{self, RegAllocAdapter};
use regalloc2::{self, Allocation, Edit, InstOrEdit, Output};

/// Word offsets of shared handlers within a shared code buffer.
pub struct SharedHandlerOffsets {
    /// Yield handler — called when fuel is exhausted.
    pub yield_handler: usize,
    /// Completion handler — called when a fiber-mode function returns.
    pub completion: usize,
    /// Interpret-exit handler — stub target for uncompiled functions.
    pub interpret_exit: usize,
}

/// Layout info for a single compiled function within the shared buffer.
pub struct FunctionLayout {
    /// Byte offset of the function body start.
    pub body_offset: usize,
}

/// Call context for PC-relative call emission in the shared code buffer.
struct CallContext<'a> {
    shared: &'a SharedHandlerOffsets,
    /// For each func_idx, `Some(word_offset)` if its body has been
    /// compiled already (enables direct BL instead of jump table hop).
    body_offsets: &'a [Option<usize>],
}

/// Byte offset of the first local in the wasm frame.
/// Layout: [prev_fp (8)][header (8)][locals...], so locals start at +16.
const FRAME_HEADER_SIZE: u16 = 16;

const CTX_IS_FIBER: u16 = std::mem::offset_of!(JitContext, is_fiber) as u16;
const CTX_RESUME_LR: u16 = std::mem::offset_of!(JitContext, resume_lr) as u16;
const CTX_JIT_SP: u16 = std::mem::offset_of!(JitContext, jit_sp) as u16;
const CTX_SAVED_FUEL: u16 = std::mem::offset_of!(JitContext, saved_fuel) as u16;
const CTX_SAVED_FP: u16 = std::mem::offset_of!(JitContext, saved_fp) as u16;
const CTX_HOST_SP: u16 = std::mem::offset_of!(JitContext, host_sp) as u16;
const CTX_HOST_FP: u16 = std::mem::offset_of!(JitContext, host_fp) as u16;
const CTX_HOST_CTX: u16 = std::mem::offset_of!(JitContext, host_ctx) as u16;
const CTX_WASM_SP_OFF: u16 = std::mem::offset_of!(JitContext, wasm_sp_off) as u16;
const CTX_SCRATCH: u16 = std::mem::offset_of!(JitContext, scratch) as u16;

// ============================================================
// regalloc2-based lowering
// ============================================================

/// State for deferred compare-and-branch fusion.
///
/// When a `Cmp` instruction is lowered, we emit `cmp` but defer `cset`.
/// If the very next item from regalloc2's output is a `BrIfZero` or
/// `BrIfNonZero` (no edits in between), we fuse into a single `b.cond`.
struct PendingCmp {
    arm_cond: Cond,
    dst_reg: Reg,
}

/// Flush a pending cmp by emitting `cset` if one exists.
fn flush_pending_cmp(e: &mut Emitter, pending: &mut Option<PendingCmp>) {
    if let Some(cmp) = pending.take() {
        e.cset_w(cmp.dst_reg, cmp.arm_cond);
    }
}

/// Convert a regalloc2 `Allocation` to our `Reg` type.
fn alloc_to_reg(alloc: Allocation) -> Reg {
    let preg = alloc
        .as_reg()
        .unwrap_or_else(|| panic!("expected register allocation, got {alloc:?}"));
    Reg(preg.hw_enc() as u8)
}

/// Compute the byte offset of a regalloc2 spill slot in the wasm frame.
///
/// Spill slots go after locals and IR merge-point slots:
/// `[header (16)][locals][ir_spills][ra2_spills]`
fn ra2_spill_offset(slot: regalloc2::SpillSlot, ra2_spill_base: u16) -> u16 {
    FRAME_HEADER_SIZE + (ra2_spill_base + slot.index() as u16) * 8
}

/// Emit a regalloc2 `Edit::Move` — copy a value between registers
/// and/or spill slots.
fn emit_edit(e: &mut Emitter, edit: &Edit, ra2_spill_base: u16) {
    match edit {
        Edit::Move { from, to } => {
            let from_reg = from.as_reg().map(|p| Reg(p.hw_enc() as u8));
            let to_reg = to.as_reg().map(|p| Reg(p.hw_enc() as u8));
            let from_slot = from.as_stack();
            let to_slot = to.as_stack();

            match (from_reg, to_reg, from_slot, to_slot) {
                (Some(fr), Some(tr), _, _) => {
                    if fr != tr {
                        e.mov_x(tr, fr);
                    }
                }
                (Some(fr), _, _, Some(ts)) => {
                    e.str_x_uoff(fr, Reg::X29, ra2_spill_offset(ts, ra2_spill_base));
                }
                (_, Some(tr), Some(fs), _) => {
                    e.ldr_x_uoff(tr, Reg::X29, ra2_spill_offset(fs, ra2_spill_base));
                }
                _ => panic!("stack-to-stack move should not be emitted by regalloc2"),
            }
        }
    }
}

/// Lower the IR body using regalloc2 allocations.
///
/// Iterates blocks in order, using `Output::block_insts_and_edits` to
/// interleave instruction emission with regalloc2-inserted moves.
/// Preserves compare-and-branch fusion via a `PendingCmp` mechanism.
fn lower_body_ra2(
    e: &mut Emitter,
    _ir: &IrFunction,
    cfg: &CfgInfo,
    adapter: &RegAllocAdapter,
    output: &Output,
    fuel_sites: &mut Vec<FuelCheckSite>,
    label_offsets: &mut [Option<usize>],
    label_patches: &mut Vec<(Label, PatchPoint)>,
    call_ctx: &CallContext,
    ra2_spill_base: u16,
    emit_markers: bool,
) {
    for block_idx in 0..cfg.blocks.len() {
        let block = regalloc2::Block::new(block_idx);
        let mut pending_cmp: Option<PendingCmp> = None;

        for item in output.block_insts_and_edits(adapter, block) {
            match item {
                InstOrEdit::Edit(edit) => {
                    flush_pending_cmp(e, &mut pending_cmp);
                    emit_edit(e, edit, ra2_spill_base);
                }
                InstOrEdit::Inst(inst) => {
                    let allocs = output.inst_allocs(inst);
                    let ir_inst = &cfg.insts[inst.index()];

                    if emit_markers {
                        e.mark();
                    }

                    match ir_inst {
                        IrInst::IConst { val, .. } => {
                            flush_pending_cmp(e, &mut pending_cmp);
                            let dst = alloc_to_reg(allocs[0]);
                            emit_i64_const(e, dst, *val);
                        }

                        IrInst::LocalGet { idx, .. } => {
                            flush_pending_cmp(e, &mut pending_cmp);
                            let dst = alloc_to_reg(allocs[0]);
                            let offset = (*idx as u16) * 8 + FRAME_HEADER_SIZE;
                            e.ldr_x_uoff(dst, Reg::X29, offset);
                        }

                        IrInst::LocalSet { idx, .. } => {
                            flush_pending_cmp(e, &mut pending_cmp);
                            let src = alloc_to_reg(allocs[0]);
                            let offset = (*idx as u16) * 8 + FRAME_HEADER_SIZE;
                            e.str_x_uoff(src, Reg::X29, offset);
                        }

                        IrInst::Add { .. } => {
                            flush_pending_cmp(e, &mut pending_cmp);
                            let dst = alloc_to_reg(allocs[0]);
                            let lhs = alloc_to_reg(allocs[1]);
                            let rhs = alloc_to_reg(allocs[2]);
                            e.add_w(dst, lhs, rhs);
                        }

                        IrInst::Sub { .. } => {
                            flush_pending_cmp(e, &mut pending_cmp);
                            let dst = alloc_to_reg(allocs[0]);
                            let lhs = alloc_to_reg(allocs[1]);
                            let rhs = alloc_to_reg(allocs[2]);
                            e.sub_w(dst, lhs, rhs);
                        }

                        IrInst::Cmp { cond, .. } => {
                            flush_pending_cmp(e, &mut pending_cmp);
                            let dst = alloc_to_reg(allocs[0]);
                            let lhs = alloc_to_reg(allocs[1]);
                            let rhs = alloc_to_reg(allocs[2]);
                            let arm_cond = match cond {
                                IrCond::Eq => Cond::EQ,
                                IrCond::LeS => Cond::LE,
                            };
                            e.cmp_w_reg(lhs, rhs);
                            pending_cmp = Some(PendingCmp {
                                arm_cond,
                                dst_reg: dst,
                            });
                        }

                        IrInst::DefLabel { label } => {
                            flush_pending_cmp(e, &mut pending_cmp);
                            label_offsets[label.0 as usize] = Some(e.offset());
                        }

                        IrInst::Br { label } => {
                            flush_pending_cmp(e, &mut pending_cmp);
                            if let Some(target) = label_offsets[label.0 as usize] {
                                let current = e.offset();
                                let word_offset = target as i32 - current as i32;
                                e.b_offset(word_offset);
                            } else {
                                let pp = e.b();
                                label_patches.push((*label, pp));
                            }
                        }

                        IrInst::BrIfZero { label, .. } => {
                            if let Some(cmp) = pending_cmp.take() {
                                // Fuse: cmp already set flags, emit b.cond.
                                // BrIfZero branches when zero → invert cond.
                                emit_b_cond(
                                    e,
                                    cmp.arm_cond.invert(),
                                    *label,
                                    label_offsets,
                                    label_patches,
                                );
                            } else {
                                let cond_reg = alloc_to_reg(allocs[0]);
                                emit_cbz_w(e, cond_reg, *label, label_offsets, label_patches);
                            }
                        }

                        IrInst::BrIfNonZero { label, .. } => {
                            if let Some(cmp) = pending_cmp.take() {
                                // Fuse: cmp already set flags, emit b.cond.
                                emit_b_cond(
                                    e,
                                    cmp.arm_cond,
                                    *label,
                                    label_offsets,
                                    label_patches,
                                );
                            } else {
                                let cond_reg = alloc_to_reg(allocs[0]);
                                emit_cbnz_w(e, cond_reg, *label, label_offsets, label_patches);
                            }
                        }

                        IrInst::FrameStore { slot, .. } => {
                            flush_pending_cmp(e, &mut pending_cmp);
                            let src = alloc_to_reg(allocs[0]);
                            e.str_x_uoff(
                                src,
                                Reg::X29,
                                (*slot as u16) * 8 + FRAME_HEADER_SIZE,
                            );
                        }

                        IrInst::FrameLoad { slot, .. } => {
                            flush_pending_cmp(e, &mut pending_cmp);
                            let dst = alloc_to_reg(allocs[0]);
                            e.ldr_x_uoff(
                                dst,
                                Reg::X29,
                                (*slot as u16) * 8 + FRAME_HEADER_SIZE,
                            );
                        }

                        IrInst::Call {
                            func_idx,
                            frame_advance,
                            ..
                        } => {
                            flush_pending_cmp(e, &mut pending_cmp);
                            // Args placed by regalloc2 via fixed-reg constraints
                            // and Edit::Move before this instruction.
                            let advance = *frame_advance as u16;
                            e.add_x_imm(Reg::X29, Reg::X29, advance);

                            if let Some(body_word) = call_ctx.body_offsets[*func_idx as usize] {
                                let current = e.offset();
                                let target = body_word as i32 - current as i32;
                                e.bl_offset(target);
                            } else {
                                let current = e.offset();
                                let target = *func_idx as i32 - current as i32;
                                e.bl_offset(target);
                            }

                            e.sub_x_imm(Reg::X29, Reg::X29, advance);
                            // Result in x9 via fixed-def; regalloc2 emits
                            // moves after this if needed.
                        }

                        IrInst::Return { .. } => {
                            flush_pending_cmp(e, &mut pending_cmp);
                            // Result already in x9 via fixed-use constraint.
                            e.ldr_x_post(Reg::X30, Reg::SP, 16);
                            e.ret();
                        }

                        IrInst::FuelCheck { cost } => {
                            flush_pending_cmp(e, &mut pending_cmp);
                            emit_fuel_check(e, fuel_sites, *cost);
                        }

                        IrInst::Trap => {
                            flush_pending_cmp(e, &mut pending_cmp);
                            e.code.push(0xD4200020); // BRK #1
                        }
                    }
                }
            }
        }

        flush_pending_cmp(e, &mut pending_cmp);
    }
}

// ============================================================
// Branch helpers
// ============================================================

/// Emit a conditional branch to a label (forward or backward).
fn emit_b_cond(
    e: &mut Emitter,
    cond: Cond,
    label: Label,
    label_offsets: &[Option<usize>],
    label_patches: &mut Vec<(Label, PatchPoint)>,
) {
    if let Some(target) = label_offsets[label.0 as usize] {
        let current = e.offset();
        let word_offset = target as i32 - current as i32;
        e.b_cond_offset(cond, word_offset);
    } else {
        let pp = e.b_cond(cond);
        label_patches.push((label, pp));
    }
}

/// Emit cbz (32-bit) to a label (forward or backward).
fn emit_cbz_w(
    e: &mut Emitter,
    rt: Reg,
    label: Label,
    label_offsets: &[Option<usize>],
    label_patches: &mut Vec<(Label, PatchPoint)>,
) {
    if let Some(target) = label_offsets[label.0 as usize] {
        let current = e.offset();
        let word_offset = target as i32 - current as i32;
        let imm19 = ((word_offset as u32) & 0x7FFFF) << 5;
        e.code.push(0x34000000 | imm19 | (rt.0 as u32 & 0x1F));
    } else {
        let pp = e.cbz_w(rt);
        label_patches.push((label, pp));
    }
}

/// Emit cbnz (32-bit) to a label (forward or backward).
fn emit_cbnz_w(
    e: &mut Emitter,
    rt: Reg,
    label: Label,
    label_offsets: &[Option<usize>],
    label_patches: &mut Vec<(Label, PatchPoint)>,
) {
    if let Some(target) = label_offsets[label.0 as usize] {
        let current = e.offset();
        let word_offset = target as i32 - current as i32;
        let imm19 = ((word_offset as u32) & 0x7FFFF) << 5;
        e.code.push(0x35000000 | imm19 | (rt.0 as u32 & 0x1F));
    } else {
        let pp = e.cbnz_w(rt);
        label_patches.push((label, pp));
    }
}

// ============================================================
// Shared code buffer mode
// ============================================================

/// Emit the shared preamble into an emitter: jump table, interpret
/// stubs, and shared handlers (yield, completion, interpret-exit).
///
/// Returns the handler offsets. The jump table starts at word offset 0
/// and has one `b <stub>` instruction per function.
pub fn emit_shared_preamble(e: &mut Emitter, func_count: usize) -> SharedHandlerOffsets {
    let jump_table_pps: Vec<PatchPoint> = (0..func_count).map(|_| e.b()).collect();

    let mut interpret_exit_pps: Vec<PatchPoint> = Vec::with_capacity(func_count);
    for (i, jt_pp) in jump_table_pps.iter().enumerate() {
        e.patch(*jt_pp);
        emit_i32_const_reg(e, Reg::W0, i as i32);
        interpret_exit_pps.push(e.b());
    }

    let yield_handler = e.offset();
    e.ldr_x_uoff(Reg::X0, Reg::X20, CTX_IS_FIBER);
    let fiber_branch = e.cbnz_x(Reg::X0);
    emit_i32_const_reg(e, Reg::W0, -1);
    e.ldr_x_post(Reg::X30, Reg::SP, 16);
    e.ret();
    e.patch(fiber_branch);
    emit_fiber_yield(e);

    let completion = e.offset();
    emit_fiber_complete(e);

    let interpret_exit = e.offset();
    e.code.push(0xD4200040); // BRK #2

    for pp in interpret_exit_pps {
        e.patch_to(pp, interpret_exit);
    }

    SharedHandlerOffsets {
        yield_handler,
        completion,
        interpret_exit,
    }
}

/// Lower an IR function into a shared emitter using PC-relative calls
/// through the jump table.
///
/// Uses regalloc2 for register allocation. The emitter must already
/// contain the shared preamble (jump table + stubs + handlers).
pub fn lower_into(
    e: &mut Emitter,
    ir: &IrFunction,
    func_idx: u32,
    shared: &SharedHandlerOffsets,
    body_offsets: &mut [Option<usize>],
    emit_markers: bool,
) -> FunctionLayout {
    let body_start = e.offset();
    body_offsets[func_idx as usize] = Some(body_start);

    // ---- Build CFG and run regalloc2 ----
    let cfg = cfg::build_cfg(&ir.insts);
    let adapter = RegAllocAdapter::new(&cfg, ir);
    let env = regalloc_adapter::build_machine_env();
    let opts = regalloc2::RegallocOptions::default();
    let output = regalloc2::run(&adapter, &env, &opts).expect("regalloc2 failed");

    // regalloc2 spill slots go after locals + IR merge-point slots.
    let ra2_spill_base = (ir.total_local_count + ir.max_operand_depth) as u16;

    // Label tracking.
    let max_label = count_labels(&cfg.insts);
    let mut label_offsets: Vec<Option<usize>> = vec![None; max_label as usize];
    let mut label_patches: Vec<(Label, PatchPoint)> = Vec::new();

    // Fuel check sites for cold stubs.
    let mut fuel_sites: Vec<FuelCheckSite> = Vec::new();

    // ---- Prologue ----
    if emit_markers {
        e.mark();
    }
    e.str_x_pre(Reg::X30, Reg::SP, -16);

    for i in 0..ir.param_count {
        let src = Reg(9 + i as u8);
        e.str_x_uoff(src, Reg::X29, (i as u16) * 8 + 16);
    }

    let extra_locals = ir.total_local_count - ir.param_count;
    for i in 0..extra_locals {
        let offset = ((ir.param_count + i) as u16) * 8 + 16;
        e.str_x_uoff(Reg::XZR, Reg::X29, offset);
    }

    // ---- Lower body ----
    lower_body_ra2(
        e,
        ir,
        &cfg,
        &adapter,
        &output,
        &mut fuel_sites,
        &mut label_offsets,
        &mut label_patches,
        &CallContext {
            shared,
            body_offsets,
        },
        ra2_spill_base,
        emit_markers,
    );

    // ---- Cold fuel-check stubs ----
    for site in &fuel_sites {
        e.patch(site.b_le_patch);
        let current = e.offset();
        let yield_offset = shared.yield_handler as i32 - current as i32;
        e.bl_offset(yield_offset);
        let current = e.offset();
        let offset = site.resume_offset as i32 - current as i32;
        e.b_offset(offset);
    }

    // Patch forward label branches.
    for (label, pp) in label_patches {
        let target = label_offsets[label.0 as usize]
            .unwrap_or_else(|| panic!("unresolved label L{}", label.0));
        e.patch_to(pp, target);
    }

    FunctionLayout {
        body_offset: body_start * 4,
    }
}

/// Patch a jump table entry to point to a new target (word offset).
pub fn patch_jump_table(e: &mut Emitter, func_idx: u32, target_word: usize) {
    let source = func_idx as usize;
    let word_offset = target_word as i32 - source as i32;
    let imm26 = (word_offset as u32) & 0x03FF_FFFF;
    e.code[source] = 0x14000000 | imm26;
}

// ============================================================
// Fuel check, constants, fiber handlers
// ============================================================

/// Info for a fuel check that needs cold-path patching.
struct FuelCheckSite {
    b_le_patch: PatchPoint,
    resume_offset: usize,
}

/// Emit a fuel check: `subs x21, x21, #cost; bc.le <cold_stub>`.
fn emit_fuel_check(e: &mut Emitter, fuel_sites: &mut Vec<FuelCheckSite>, cost: u32) {
    e.subs_x_imm(Reg::X21, Reg::X21, cost as u16);
    let b_le_patch = e.b_cond(Cond::LE);
    let resume_offset = e.offset();
    fuel_sites.push(FuelCheckSite {
        b_le_patch,
        resume_offset,
    });
}

fn emit_fiber_yield(e: &mut Emitter) {
    e.str_x_uoff(Reg::X30, Reg::X20, CTX_RESUME_LR);
    e.stp_x_soff(Reg::X9, Reg::X10, Reg::X20, CTX_SCRATCH as i16);
    e.stp_x_soff(Reg(11), Reg(12), Reg::X20, (CTX_SCRATCH + 16) as i16);
    e.stp_x_soff(Reg(13), Reg(14), Reg::X20, (CTX_SCRATCH + 32) as i16);
    e.str_x_uoff(Reg(15), Reg::X20, CTX_SCRATCH + 48);
    e.mov_x_from_sp(Reg::X9);
    e.str_x_uoff(Reg::X9, Reg::X20, CTX_JIT_SP);
    e.str_x_uoff(Reg::X21, Reg::X20, CTX_SAVED_FUEL);
    e.str_x_uoff(Reg::X29, Reg::X20, CTX_SAVED_FP);
    e.ldr_x_uoff(Reg::X9, Reg::X20, CTX_HOST_SP);
    e.ldp_x_soff(Reg::X29, Reg::X30, Reg::X20, CTX_HOST_FP as i16);
    e.ldr_x_uoff(Reg::X20, Reg::X20, CTX_HOST_CTX);
    e.mov_sp_from(Reg::X9);
    e.movz_w(Reg::W0, 0);
    e.ret();
}

fn emit_fiber_complete(e: &mut Emitter) {
    e.str_x_uoff(Reg::X9, Reg::X20, CTX_WASM_SP_OFF);
    e.ldr_x_uoff(Reg::X9, Reg::X20, CTX_HOST_SP);
    e.ldp_x_soff(Reg::X29, Reg::X30, Reg::X20, CTX_HOST_FP as i16);
    e.ldr_x_uoff(Reg::X20, Reg::X20, CTX_HOST_CTX);
    e.mov_sp_from(Reg::X9);
    e.movz_w(Reg::W0, 1);
    e.ret();
}

fn emit_i32_const_reg(e: &mut Emitter, rd: Reg, val: i32) {
    if val >= 0 && val < 65536 {
        e.movz_w(rd, val as u16);
    } else if val < 0 && val >= -65536 {
        e.movn_w(rd, (!val) as u16);
    } else {
        let lo = (val as u32) & 0xFFFF;
        let hi = ((val as u32) >> 16) & 0xFFFF;
        e.movz_w(rd, lo as u16);
        if hi != 0 {
            let inst = 0x72A00000 | (hi << 5) | (rd.0 as u32 & 0x1F);
            e.code.push(inst);
        }
    }
}

fn emit_i64_const(e: &mut Emitter, rd: Reg, val: i64) {
    if val >= 0 && val < 65536 {
        e.movz_x(rd, val as u16);
    } else {
        emit_i32_const_reg(e, rd, val as i32);
    }
}

/// Count the maximum Label index + 1.
fn count_labels(insts: &[IrInst]) -> u32 {
    let mut max_label = 0u32;
    for inst in insts {
        match inst {
            IrInst::DefLabel { label }
            | IrInst::Br { label }
            | IrInst::BrIfZero { label, .. }
            | IrInst::BrIfNonZero { label, .. } => {
                max_label = max_label.max(label.0 + 1);
            }
            _ => {}
        }
    }
    max_label
}

/// Call `f` for every VReg that is *defined* by `inst`.
pub fn for_each_def(inst: &IrInst, mut f: impl FnMut(VReg)) {
    match inst {
        IrInst::IConst { dst, .. } => f(*dst),
        IrInst::LocalGet { dst, .. } => f(*dst),
        IrInst::LocalSet { .. } => {}
        IrInst::Add { dst, .. } => f(*dst),
        IrInst::Sub { dst, .. } => f(*dst),
        IrInst::Cmp { dst, .. } => f(*dst),
        IrInst::DefLabel { .. } => {}
        IrInst::Br { .. } => {}
        IrInst::BrIfZero { .. } => {}
        IrInst::BrIfNonZero { .. } => {}
        IrInst::FrameStore { .. } => {}
        IrInst::FrameLoad { dst, .. } => f(*dst),
        IrInst::Call { result, .. } => {
            if let Some(r) = result {
                f(*r);
            }
        }
        IrInst::Return { .. } => {}
        IrInst::FuelCheck { .. } => {}
        IrInst::Trap => {}
    }
}

/// Call `f` for every VReg that is *read* by `inst`.
pub fn for_each_use(inst: &IrInst, mut f: impl FnMut(VReg)) {
    match inst {
        IrInst::IConst { .. } => {}
        IrInst::LocalGet { .. } => {}
        IrInst::LocalSet { src, .. } => f(*src),
        IrInst::Add { lhs, rhs, .. } => {
            f(*lhs);
            f(*rhs);
        }
        IrInst::Sub { lhs, rhs, .. } => {
            f(*lhs);
            f(*rhs);
        }
        IrInst::Cmp { lhs, rhs, .. } => {
            f(*lhs);
            f(*rhs);
        }
        IrInst::DefLabel { .. } => {}
        IrInst::Br { .. } => {}
        IrInst::BrIfZero { cond, .. } => f(*cond),
        IrInst::BrIfNonZero { cond, .. } => f(*cond),
        IrInst::FrameStore { src, .. } => f(*src),
        IrInst::FrameLoad { .. } => {}
        IrInst::Call { args, .. } => {
            for a in args {
                f(*a);
            }
        }
        IrInst::Return { results } => {
            for r in results {
                f(*r);
            }
        }
        IrInst::FuelCheck { .. } => {}
        IrInst::Trap => {}
    }
}
