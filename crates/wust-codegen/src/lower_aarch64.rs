use crate::cfg::{self, CfgInfo};
use crate::context::JitContext;
use crate::emit::{Cond, Emitter, PatchPoint, Reg};
use crate::ir::{AluOp, IrFunction, IrInst, Label, Operand, UnaryOp};
use crate::regalloc_adapter::{self, RegAllocAdapter};
use regalloc2::{self, Allocation, Edit, InstOrEdit, Output};

/// Result of lowering a single function.
pub struct LowerResult {
    /// Word offset where the function's code starts.
    pub body_start: usize,
    /// Label index → word offset relative to `body_start`.
    pub label_offsets: Vec<Option<usize>>,
}

/// Word offsets of shared handlers within a shared code buffer.
pub struct SharedHandlerOffsets {
    /// Yield handler — called when fuel is exhausted.
    pub yield_handler: usize,
    /// Completion handler — called when a fiber-mode function returns.
    pub completion: usize,
}


/// Byte offset of the first local in the wasm frame.
/// Layout: [prev_fp (8)][header (8)][locals...], so locals start at +16.
const FRAME_HEADER_SIZE: u16 = 16;

/// Byte offset of a frame slot (local or spill) from the frame pointer.
fn frame_slot_offset(slot: u32) -> u16 {
    slot as u16 * 8 + FRAME_HEADER_SIZE
}

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

/// Flush a pending fuel consume by emitting a bare `sub` if one exists.
fn flush_pending_fuel(e: &mut Emitter, pending: &mut Option<u32>) {
    if let Some(cost) = pending.take() {
        e.sub_x_imm(Reg::X21, Reg::X21, cost as u16);
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
    cfg: &CfgInfo,
    adapter: &RegAllocAdapter,
    output: &Output,
    fuel_sites: &mut Vec<FuelCheckSite>,
    label_offsets: &mut [Option<usize>],
    label_patches: &mut Vec<(Label, PatchPoint)>,
    body_offsets: &[Option<usize>],
    ra2_spill_base: u16,
    min_call_frame_advance: u16,
    emit_markers: bool,
) {
    // For each block, find the label at the start of the next block
    // (if any). Used to skip redundant fallthrough branches.
    let next_block_label: Vec<Option<Label>> = (0..cfg.blocks.len())
        .map(|bi| {
            let next_bi = bi + 1;
            if next_bi >= cfg.blocks.len() {
                return None;
            }
            let next_start = cfg.blocks[next_bi].inst_start as usize;
            match &cfg.insts[next_start] {
                IrInst::DefLabel { label, .. } => Some(*label),
                _ => None,
            }
        })
        .collect();

    // Track whether any `bl` has been emitted so far (Call or
    // FuelCheck cold path). When true, Return must reload x30 from
    // the stack before `ret`. When false, x30 is still valid.
    let mut lr_clobbered = false;

    for block_idx in 0..cfg.blocks.len() {
        let block = regalloc2::Block::new(block_idx);
        let mut pending_cmp: Option<PendingCmp> = None;
        let mut pending_fuel: Option<u32> = None;

        // Record label offset at the start of the block, before any
        // regalloc2 entry edits. Branch targets must land before the
        // block-param moves so that incoming edges execute them.
        let first_inst = cfg.blocks[block_idx].inst_start as usize;
        if let IrInst::DefLabel { label, .. } = &cfg.insts[first_inst] {
            label_offsets[label.0 as usize] = Some(e.offset());
        }

        for item in output.block_insts_and_edits(adapter, block) {
            match item {
                InstOrEdit::Edit(edit) => {
                    flush_pending_cmp(e, &mut pending_cmp);
                    flush_pending_fuel(e, &mut pending_fuel);
                    emit_edit(e, edit, ra2_spill_base);
                }
                InstOrEdit::Inst(inst) => {
                    let allocs = output.inst_allocs(inst);
                    let ir_inst = &cfg.insts[inst.index()];

                    if emit_markers {
                        e.mark();
                    }

                    // Flush pending cmp unless this instruction fuses with it.
                    let fuses_cmp = matches!(
                        ir_inst,
                        IrInst::BrIfZero { .. } | IrInst::BrIfNonZero { .. }
                    );
                    if !fuses_cmp {
                        flush_pending_cmp(e, &mut pending_cmp);
                    }

                    // Flush pending fuel unless this is a FuelCheck (fuses).
                    let fuses_fuel = matches!(ir_inst, IrInst::FuelCheck { .. });
                    if !fuses_fuel {
                        flush_pending_fuel(e, &mut pending_fuel);
                    }

                    match ir_inst {
                        IrInst::IConst { val, .. } => {
                            let dst = alloc_to_reg(allocs[0]);
                            emit_i64_const(e, dst, *val);
                        }

                        // ParamDef: value is already in the param register
                        // from the calling convention. Nothing to emit.
                        IrInst::ParamDef { .. } => {}

                        IrInst::LocalGet { idx, .. } => {
                            let dst = alloc_to_reg(allocs[0]);
                            e.ldr_x_uoff(dst, Reg::X29, frame_slot_offset(*idx));
                        }

                        IrInst::LocalSet { idx, .. } => {
                            let src = alloc_to_reg(allocs[0]);
                            e.str_x_uoff(src, Reg::X29, frame_slot_offset(*idx));
                        }

                        IrInst::Alu { op, rhs, .. } => {
                            let dst = alloc_to_reg(allocs[0]);
                            let lhs = alloc_to_reg(allocs[1]);
                            match rhs {
                                Operand::Reg(_) => {
                                    let rhs_reg = alloc_to_reg(allocs[2]);
                                    lower_alu_reg(e, *op, dst, lhs, rhs_reg, &mut pending_cmp);
                                }
                                Operand::Imm(imm) => {
                                    lower_alu_imm(e, *op, dst, lhs, *imm, &mut pending_cmp);
                                }
                            }
                        }

                        IrInst::Unary { op, .. } => {
                            let dst = alloc_to_reg(allocs[0]);
                            let src = alloc_to_reg(allocs[1]);
                            lower_unary(e, *op, dst, src);
                        }

                        IrInst::DefLabel { .. } => {
                            // Label offset already recorded at block start
                            // (before entry edits) — see above.
                        }

                        IrInst::Br { label, .. } => {
                            // Skip redundant fallthrough branches — the
                            // target is the very next block's DefLabel.
                            let is_fallthrough =
                                next_block_label[block_idx] == Some(*label);
                            if !is_fallthrough {
                                emit_branch_to_label(
                                    e, *label, label_offsets, label_patches,
                                    |e, off| e.b_offset(off),
                                    |e| e.b(),
                                );
                            }
                        }

                        IrInst::BrIfZero { label, .. } => {
                            if let Some(cmp) = pending_cmp.take() {
                                let c = cmp.arm_cond.invert();
                                emit_branch_to_label(
                                    e, *label, label_offsets, label_patches,
                                    |e, off| e.b_cond_offset(c, off),
                                    |e| e.b_cond(c),
                                );
                            } else {
                                let rt = alloc_to_reg(allocs[0]);
                                emit_branch_to_label(
                                    e, *label, label_offsets, label_patches,
                                    |e, off| e.cbz_w_offset(rt, off),
                                    |e| e.cbz_w(rt),
                                );
                            }
                        }

                        IrInst::BrIfNonZero { label, .. } => {
                            if let Some(cmp) = pending_cmp.take() {
                                let c = cmp.arm_cond;
                                emit_branch_to_label(
                                    e, *label, label_offsets, label_patches,
                                    |e, off| e.b_cond_offset(c, off),
                                    |e| e.b_cond(c),
                                );
                            } else {
                                let rt = alloc_to_reg(allocs[0]);
                                emit_branch_to_label(
                                    e, *label, label_offsets, label_patches,
                                    |e, off| e.cbnz_w_offset(rt, off),
                                    |e| e.cbnz_w(rt),
                                );
                            }
                        }

                        IrInst::FrameStore { slot, .. } => {
                            let src = alloc_to_reg(allocs[0]);
                            e.str_x_uoff(src, Reg::X29, frame_slot_offset(*slot));
                        }

                        IrInst::FrameLoad { slot, .. } => {
                            let dst = alloc_to_reg(allocs[0]);
                            e.ldr_x_uoff(dst, Reg::X29, frame_slot_offset(*slot));
                        }

                        IrInst::Call {
                            func_idx,
                            frame_advance,
                            ..
                        } => {
                            let advance =
                                (*frame_advance as u16).max(min_call_frame_advance);
                            e.add_x_imm(Reg::X29, Reg::X29, advance);

                            let target_word = body_offsets[*func_idx as usize]
                                .unwrap_or(*func_idx as usize);
                            let offset = target_word as i32 - e.offset() as i32;
                            e.bl_offset(offset);
                            lr_clobbered = true;

                            e.sub_x_imm(Reg::X29, Reg::X29, advance);
                        }

                        IrInst::Return { .. } => {
                            if lr_clobbered {
                                e.ldr_x_post(Reg::X30, Reg::SP, 16);
                            } else {
                                e.add_x_imm(Reg::SP, Reg::SP, 16);
                            }
                            e.ret();
                        }

                        IrInst::FuelConsume { cost } => {
                            // Defer — may fuse with the next FuelCheck.
                            if let Some(prev) = pending_fuel.as_mut() {
                                *prev += cost;
                            } else {
                                pending_fuel = Some(*cost);
                            }
                        }

                        IrInst::FuelCheck { .. } => {
                            if let Some(cost) = pending_fuel.take() {
                                emit_fuel_check_with_cost(e, fuel_sites, cost);
                            } else {
                                emit_fuel_check_sign(e, fuel_sites);
                            }
                            // Cold path does `bl yield_handler`.
                            lr_clobbered = true;
                        }

                        IrInst::Trap => {
                            e.brk(1);
                        }
                    }
                }
            }
        }

        flush_pending_cmp(e, &mut pending_cmp);
        flush_pending_fuel(e, &mut pending_fuel);
    }
}

// ============================================================
// Branch helpers
// ============================================================

/// Emit a branch to a label (forward or backward).
///
/// `emit_back` is called with the word offset for backward branches.
/// `emit_fwd` is called for forward branches and returns a PatchPoint.
fn emit_branch_to_label(
    e: &mut Emitter,
    label: Label,
    label_offsets: &[Option<usize>],
    label_patches: &mut Vec<(Label, PatchPoint)>,
    emit_back: impl FnOnce(&mut Emitter, i32),
    emit_fwd: impl FnOnce(&mut Emitter) -> PatchPoint,
) {
    if let Some(target) = label_offsets[label.0 as usize] {
        let word_offset = target as i32 - e.offset() as i32;
        emit_back(e, word_offset);
    } else {
        let pp = emit_fwd(e);
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
    e.brk(2);

    for pp in interpret_exit_pps {
        e.patch_to(pp, interpret_exit);
    }

    SharedHandlerOffsets {
        yield_handler,
        completion,
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
) -> LowerResult {
    let body_start = e.offset();
    body_offsets[func_idx as usize] = Some(body_start);

    // ---- Build CFG and run regalloc2 ----
    let cfg = cfg::build_cfg(&ir.insts);
    let adapter = RegAllocAdapter::new(&cfg);
    let env = regalloc_adapter::build_machine_env();
    let opts = regalloc2::RegallocOptions { validate_ssa: true, ..Default::default() };
    let output = regalloc2::run(&adapter, &env, &opts).expect("regalloc2 failed");

    // regalloc2 spill slots go after locals + IR merge-point slots.
    let ra2_spill_base = (ir.total_local_count + ir.max_operand_depth) as u16;

    // Minimum frame advance for calls. When regalloc2 uses spill slots,
    // the advance must cover them so the callee doesn't overwrite them.
    // When there are no spills, the per-call IR frame_advance is used
    // (smaller — only covers header + locals + live operand stack depth).
    let min_call_frame_advance = if output.num_spillslots > 0 {
        FRAME_HEADER_SIZE + (ra2_spill_base + output.num_spillslots as u16) * 8
    } else {
        0
    };

    // Label tracking.
    let max_label = cfg::max_label_index(&cfg.insts) + 1;
    let mut label_offsets: Vec<Option<usize>> = vec![None; max_label];
    let mut label_patches: Vec<(Label, PatchPoint)> = Vec::new();

    // Fuel check sites for cold stubs.
    let mut fuel_sites: Vec<FuelCheckSite> = Vec::new();

    // ---- Prologue ----
    // Always save LR — cheap one-time store.
    if emit_markers {
        e.mark();
    }
    e.str_x_pre(Reg::X30, Reg::SP, -16);

    // ---- Lower body ----
    lower_body_ra2(
        e,
        &cfg,
        &adapter,
        &output,
        &mut fuel_sites,
        &mut label_offsets,
        &mut label_patches,
        body_offsets,
        ra2_spill_base,
        min_call_frame_advance,
        emit_markers,
    );

    // Mark the end of the main body so the last IR region doesn't
    // extend into the cold stubs.
    if emit_markers {
        e.mark();
    }

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

    // Convert label offsets to be relative to body_start.
    let relative_label_offsets: Vec<Option<usize>> = label_offsets
        .iter()
        .map(|off| off.map(|o| o - body_start))
        .collect();

    LowerResult {
        body_start,
        label_offsets: relative_label_offsets,
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

/// Emit a fused fuel consume+check: `subs x21, x21, #cost; b.le <cold>`.
fn emit_fuel_check_with_cost(e: &mut Emitter, fuel_sites: &mut Vec<FuelCheckSite>, cost: u32) {
    e.subs_x_imm(Reg::X21, Reg::X21, cost as u16);
    let b_le_patch = e.b_cond(Cond::LE);
    let resume_offset = e.offset();
    fuel_sites.push(FuelCheckSite {
        b_le_patch,
        resume_offset,
    });
}

/// Emit a standalone fuel check (no consume): `tbnz x21, #63, <cold>`.
/// Branches if fuel is negative (sign bit set).
fn emit_fuel_check_sign(e: &mut Emitter, fuel_sites: &mut Vec<FuelCheckSite>) {
    // cmp x21, #0; b.lt cold — checks if fuel went negative.
    e.cmp_x_imm(Reg::X21, 0);
    let b_le_patch = e.b_cond(Cond::LT);
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
            e.movk_w(rd, hi as u16, 16);
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

/// Lower an ALU operation with register operand.
fn lower_alu_reg(
    e: &mut Emitter,
    op: AluOp,
    dst: Reg,
    lhs: Reg,
    rhs: Reg,
    pending_cmp: &mut Option<PendingCmp>,
) {
    match op {
        // i32 arithmetic
        AluOp::I32Add => e.add_w(dst, lhs, rhs),
        AluOp::I32Sub => e.sub_w(dst, lhs, rhs),
        AluOp::I32Mul => e.mul_w(dst, lhs, rhs),
        AluOp::I32DivS => e.sdiv_w(dst, lhs, rhs),
        AluOp::I32DivU => e.udiv_w(dst, lhs, rhs),
        AluOp::I32RemS => {
            e.sdiv_w(dst, lhs, rhs);
            e.msub_w(dst, dst, rhs, lhs);
        }
        AluOp::I32RemU => {
            e.udiv_w(dst, lhs, rhs);
            e.msub_w(dst, dst, rhs, lhs);
        }
        // i32 bitwise
        AluOp::I32And => e.and_w(dst, lhs, rhs),
        AluOp::I32Or => e.orr_w(dst, lhs, rhs),
        AluOp::I32Xor => e.eor_w(dst, lhs, rhs),
        AluOp::I32Shl => e.lsl_w(dst, lhs, rhs),
        AluOp::I32ShrS => e.asr_w(dst, lhs, rhs),
        AluOp::I32ShrU => e.lsr_w(dst, lhs, rhs),
        AluOp::I32Rotl => e.ror_w(dst, lhs, rhs), // TODO: rotl needs neg
        AluOp::I32Rotr => e.ror_w(dst, lhs, rhs),
        // i32 comparison
        AluOp::I32Eq | AluOp::I32Ne | AluOp::I32LtS | AluOp::I32LtU
        | AluOp::I32GtS | AluOp::I32GtU | AluOp::I32LeS | AluOp::I32LeU
        | AluOp::I32GeS | AluOp::I32GeU => {
            e.cmp_w_reg(lhs, rhs);
            let arm_cond = alu_op_to_cond(op);
            *pending_cmp = Some(PendingCmp { arm_cond, dst_reg: dst });
        }
        // i64 arithmetic
        AluOp::I64Add => e.add_x(dst, lhs, rhs),
        AluOp::I64Sub => e.sub_x(dst, lhs, rhs),
        AluOp::I64Mul => e.mul_x(dst, lhs, rhs),
        AluOp::I64DivS => e.sdiv_x(dst, lhs, rhs),
        AluOp::I64DivU => e.udiv_x(dst, lhs, rhs),
        AluOp::I64RemS => {
            e.sdiv_x(dst, lhs, rhs);
            e.msub_x(dst, dst, rhs, lhs);
        }
        AluOp::I64RemU => {
            e.udiv_x(dst, lhs, rhs);
            e.msub_x(dst, dst, rhs, lhs);
        }
        // i64 bitwise
        AluOp::I64And => e.and_x(dst, lhs, rhs),
        AluOp::I64Or => e.orr_x(dst, lhs, rhs),
        AluOp::I64Xor => e.eor_x(dst, lhs, rhs),
        AluOp::I64Shl => e.lsl_x(dst, lhs, rhs),
        AluOp::I64ShrS => e.asr_x(dst, lhs, rhs),
        AluOp::I64ShrU => e.lsr_x(dst, lhs, rhs),
        AluOp::I64Rotl => e.ror_x(dst, lhs, rhs), // TODO: rotl needs neg
        AluOp::I64Rotr => e.ror_x(dst, lhs, rhs),
        // i64 comparison
        AluOp::I64Eq | AluOp::I64Ne | AluOp::I64LtS | AluOp::I64LtU
        | AluOp::I64GtS | AluOp::I64GtU | AluOp::I64LeS | AluOp::I64LeU
        | AluOp::I64GeS | AluOp::I64GeU => {
            e.cmp_x_reg(lhs, rhs);
            let arm_cond = alu_op_to_cond(op);
            *pending_cmp = Some(PendingCmp { arm_cond, dst_reg: dst });
        }
    }
}

/// Lower an ALU operation with immediate operand.
fn lower_alu_imm(
    e: &mut Emitter,
    op: AluOp,
    dst: Reg,
    lhs: Reg,
    imm: i64,
    pending_cmp: &mut Option<PendingCmp>,
) {
    let is_cmp = matches!(op,
        AluOp::I32Eq | AluOp::I32Ne | AluOp::I32LtS | AluOp::I32LtU
        | AluOp::I32GtS | AluOp::I32GtU | AluOp::I32LeS | AluOp::I32LeU
        | AluOp::I32GeS | AluOp::I32GeU
        | AluOp::I64Eq | AluOp::I64Ne | AluOp::I64LtS | AluOp::I64LtU
        | AluOp::I64GtS | AluOp::I64GtU | AluOp::I64LeS | AluOp::I64LeU
        | AluOp::I64GeS | AluOp::I64GeU
    );
    if is_cmp {
        let is_64 = matches!(op,
            AluOp::I64Eq | AluOp::I64Ne | AluOp::I64LtS | AluOp::I64LtU
            | AluOp::I64GtS | AluOp::I64GtU | AluOp::I64LeS | AluOp::I64LeU
            | AluOp::I64GeS | AluOp::I64GeU
        );
        if is_64 {
            e.cmp_x_imm(lhs, imm as u16);
        } else {
            e.cmp_w_imm(lhs, imm as u16);
        }
        let arm_cond = alu_op_to_cond(op);
        *pending_cmp = Some(PendingCmp { arm_cond, dst_reg: dst });
        return;
    }

    match op {
        AluOp::I32Add => e.add_w_imm(dst, lhs, imm as u16),
        AluOp::I32Sub => e.sub_w_imm(dst, lhs, imm as u16),
        AluOp::I64Add => e.add_x_imm(dst, lhs, imm as u16),
        AluOp::I64Sub => e.sub_x_imm(dst, lhs, imm as u16),
        _ => e.brk(1),
    }
}

/// Map an ALU comparison op to an AArch64 condition code.
fn alu_op_to_cond(op: AluOp) -> Cond {
    match op {
        AluOp::I32Eq | AluOp::I64Eq => Cond::EQ,
        AluOp::I32Ne | AluOp::I64Ne => Cond::NE,
        AluOp::I32LtS | AluOp::I64LtS => Cond::LT,
        AluOp::I32LtU | AluOp::I64LtU => Cond::CC,
        AluOp::I32GtS | AluOp::I64GtS => Cond::GT,
        AluOp::I32GtU | AluOp::I64GtU => Cond::HI,
        AluOp::I32LeS | AluOp::I64LeS => Cond::LE,
        AluOp::I32LeU | AluOp::I64LeU => Cond::LS,
        AluOp::I32GeS | AluOp::I64GeS => Cond::GE,
        AluOp::I32GeU | AluOp::I64GeU => Cond::CS,
        _ => unreachable!("not a comparison op: {op}"),
    }
}

/// Lower a unary operation.
fn lower_unary(e: &mut Emitter, op: UnaryOp, dst: Reg, src: Reg) {
    match op {
        UnaryOp::I32Eqz => {
            e.cmp_w_imm(src, 0);
            e.cset_w(dst, Cond::EQ);
        }
        UnaryOp::I64Eqz => {
            e.cmp_x_imm(src, 0);
            e.cset_w(dst, Cond::EQ);
        }
        UnaryOp::I32Clz => e.clz_w(dst, src),
        UnaryOp::I64Clz => e.clz_x(dst, src),
        UnaryOp::I32Ctz => {
            e.rbit_w(dst, src);
            e.clz_w(dst, dst);
        }
        UnaryOp::I64Ctz => {
            e.rbit_x(dst, src);
            e.clz_x(dst, dst);
        }
        UnaryOp::I32Popcnt | UnaryOp::I64Popcnt => {
            let v0 = Reg(0);
            e.fmov_d_from_x(v0, src);
            e.cnt_8b(v0, v0);
            e.addv_8b(v0, v0);
            e.umov_w_b0(dst, v0);
        }
        UnaryOp::I32WrapI64 => {
            if dst != src {
                e.mov_w(dst, src);
            }
        }
        UnaryOp::I64ExtendI32S => e.sxtw(dst, src),
        UnaryOp::I64ExtendI32U => e.uxtw(dst, src),
        UnaryOp::I32Extend8S => e.sxtb_w(dst, src),
        UnaryOp::I32Extend16S => e.sxth_w(dst, src),
        UnaryOp::I64Extend8S => e.sxtb_x(dst, src),
        UnaryOp::I64Extend16S => e.sxth_x(dst, src),
        UnaryOp::I64Extend32S => e.sxtw(dst, src),
    }
}

