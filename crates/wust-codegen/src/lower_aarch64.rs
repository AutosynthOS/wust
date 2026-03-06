use crate::emit::{Cond, Emitter, PatchPoint, Reg};
use crate::ir::{AluOp, IrFunction, IrInst, Label, Operand, UnaryOp, VReg};

/// Physical scratch registers available for allocation (x9–x15).
const SCRATCH_REGS: [Reg; 7] = [Reg(9), Reg(10), Reg(11), Reg(12), Reg(13), Reg(14), Reg(15)];
// TODO: x0-x8 and x28 are all free scratch registers. x28 was previously
// reserved for saved host SP (longjmp suspend), but suspend now unwinds via
// normal returns so x28 is unused. Host SP belongs in the Context struct.

/// Result of lowering a single function.
pub struct LowerResult {
    /// Word offset where the function's code starts.
    pub body_start: usize,
    /// Label index → word offset relative to `body_start`.
    pub label_offsets: Vec<Option<usize>>,
    /// Per-word annotations: (word_offset_relative_to_body_start, label).
    pub word_labels: Vec<(usize, String)>,
}

/// Word offsets of shared code regions within the code buffer.
pub struct SharedHandlerOffsets {
    /// Word offset immediately after the last shared preamble instruction.
    pub end: usize,
}

// ============================================================
// VReg → physical register mapping
// ============================================================

/// How to reload a VReg that has been evicted from all physical registers.
#[derive(Clone, Copy, Debug)]
enum ReloadSource {
    /// Not yet defined, or must be spilled before it can be reloaded.
    None,
    /// Re-emit a constant (from IConst).
    Const(i64),
    /// Reload from a known frame slot: `[g.lb + offset]` with the given width.
    Frame { offset: u16, size: u8 },
    /// Was spilled to a dynamically allocated frame slot during eviction.
    Spill { offset: u16 },
}

/// Result of allocating a register for a VReg.
enum AllocResult {
    /// Register was free or vreg already mapped.
    Ready(Reg),
    /// Had to evict a vreg — caller must spill before writing.
    Evicted { reg: Reg, evicted: VReg },
    /// Moved occupant to a free register to satisfy hint.
    /// Caller emits `mov_sized(mov.0, mov.1, size)`, then writes to `reg`.
    Relocated { reg: Reg, mov: (Reg, Reg), size: u8 },
}

/// Tracks which physical register holds each VReg, with LRU eviction.
struct RegMap {
    /// VReg index → physical register index into SCRATCH_REGS (or None).
    vreg_to_idx: Vec<Option<u8>>,
    /// For each SCRATCH_REGS slot: which VReg it holds (or None).
    slot_vreg: [Option<u32>; 7],
    /// Monotonic use counter for LRU eviction.
    use_tick: u32,
    /// Per-slot last-use tick.
    slot_tick: [u32; 7],
    /// For each VReg: how to reload it after eviction.
    reload_source: Vec<ReloadSource>,
    /// For each VReg: value size in bytes (4 for i32, 8 for i64). Default 8.
    vreg_size: Vec<u8>,
    /// Next available spill slot offset from g.lb (grows upward from frame_size).
    next_spill_offset: u16,
}

impl RegMap {
    fn new(vreg_count: u32, frame_size: u16) -> Self {
        RegMap {
            vreg_to_idx: vec![None; vreg_count as usize],
            slot_vreg: [None; 7],
            use_tick: 0,
            slot_tick: [0; 7],
            reload_source: vec![ReloadSource::None; vreg_count as usize],
            vreg_size: vec![8; vreg_count as usize],
            next_spill_offset: frame_size,
        }
    }

    /// Get the physical register for a VReg, if it's currently mapped.
    fn get(&mut self, vreg: VReg) -> Option<Reg> {
        if let Some(idx) = self.vreg_to_idx[vreg.0 as usize] {
            self.use_tick += 1;
            self.slot_tick[idx as usize] = self.use_tick;
            Some(SCRATCH_REGS[idx as usize])
        } else {
            None
        }
    }

    /// Assign a VReg to a specific scratch register slot.
    ///
    /// Returns the evicted VReg (if any). The caller must call
    /// `handle_eviction` for the returned VReg before writing to the
    /// register.
    fn assign(&mut self, vreg: VReg, slot_idx: u8) -> Option<VReg> {
        // Evict previous occupant if any.
        let evicted = if let Some(old_vreg) = self.slot_vreg[slot_idx as usize] {
            self.vreg_to_idx[old_vreg as usize] = None;
            Some(VReg(old_vreg))
        } else {
            None
        };
        // Clear previous mapping for this vreg.
        if let Some(old_idx) = self.vreg_to_idx[vreg.0 as usize] {
            self.slot_vreg[old_idx as usize] = None;
        }
        self.vreg_to_idx[vreg.0 as usize] = Some(slot_idx);
        self.slot_vreg[slot_idx as usize] = Some(vreg.0);
        self.use_tick += 1;
        self.slot_tick[slot_idx as usize] = self.use_tick;
        evicted
    }

    /// Allocate a register for a VReg, with an optional hint.
    ///
    /// When `hint` is Some(slot_idx), prefer that scratch register slot.
    /// If the hinted slot is occupied, the occupant is relocated to a
    /// free register (unless the occupant is itself hinted to that slot).
    fn alloc(
        &mut self,
        vreg: VReg,
        hint: Option<u8>,
        hints: &[Option<u8>],
        inst_idx: u32,
        last_use: &[u32],
    ) -> AllocResult {
        // Already mapped?
        if let Some(idx) = self.vreg_to_idx[vreg.0 as usize] {
            self.use_tick += 1;
            self.slot_tick[idx as usize] = self.use_tick;
            return AllocResult::Ready(SCRATCH_REGS[idx as usize]);
        }
        // Try hinted slot.
        if let Some(h) = hint {
            if self.slot_vreg[h as usize].is_none() {
                self.assign(vreg, h);
                return AllocResult::Ready(SCRATCH_REGS[h as usize]);
            }
            // Slot occupied — check if occupant is dead (last use ≤ now).
            if let Some(occ) = self.slot_vreg[h as usize] {
                if last_use[occ as usize] <= inst_idx {
                    // Occupant is dead — just take the register.
                    self.assign(vreg, h);
                    return AllocResult::Ready(SCRATCH_REGS[h as usize]);
                }
                // Occupant is live — try to relocate it to a free reg,
                // unless it's hinted to this same slot.
                let occ_hinted_here = hints
                    .get(occ as usize)
                    .map_or(false, |oh| *oh == Some(h));
                if !occ_hinted_here {
                    if let Some(free) = (0..7u8).find(|i| self.slot_vreg[*i as usize].is_none()) {
                        let from = SCRATCH_REGS[h as usize];
                        let to = SCRATCH_REGS[free as usize];
                        self.slot_vreg[free as usize] = Some(occ);
                        self.slot_tick[free as usize] = self.slot_tick[h as usize];
                        self.vreg_to_idx[occ as usize] = Some(free);
                        self.slot_vreg[h as usize] = None;
                        let occ_size = self.vreg_size[occ as usize];
                        self.assign(vreg, h);
                        return AllocResult::Relocated {
                            reg: from,
                            mov: (to, from),
                            size: occ_size,
                        };
                    }
                }
            }
        }
        // Find a free slot.
        for i in 0..7u8 {
            if self.slot_vreg[i as usize].is_none() {
                self.assign(vreg, i);
                return AllocResult::Ready(SCRATCH_REGS[i as usize]);
            }
        }
        // Evict LRU.
        let mut best_idx = 0u8;
        let mut best_tick = u32::MAX;
        for i in 0..7u8 {
            if self.slot_tick[i as usize] < best_tick {
                best_tick = self.slot_tick[i as usize];
                best_idx = i;
            }
        }
        let evicted = self.slot_vreg[best_idx as usize].map(VReg);
        self.assign(vreg, best_idx);
        match evicted {
            Some(v) => AllocResult::Evicted { reg: SCRATCH_REGS[best_idx as usize], evicted: v },
            None => AllocResult::Ready(SCRATCH_REGS[best_idx as usize]),
        }
    }

    /// Invalidate all mappings (e.g., after a call or at a DefLabel).
    fn invalidate_all(&mut self) {
        for i in 0..7 {
            if let Some(v) = self.slot_vreg[i] {
                self.vreg_to_idx[v as usize] = None;
            }
            self.slot_vreg[i] = None;
        }
    }
}

// ============================================================
// Compare-and-branch fusion
// ============================================================

/// State for deferred compare-and-branch fusion.
struct PendingCmp {
    arm_cond: Cond,
    dst_reg: Reg,
}

fn flush_pending_cmp(e: &mut Emitter, pending: &mut Option<PendingCmp>) {
    if let Some(cmp) = pending.take() {
        e.cset_w(cmp.dst_reg, cmp.arm_cond);
    }
}

fn flush_pending_fuel(e: &mut Emitter, pending: &mut Option<u32>) {
    if let Some(cost) = pending.take() {
        e.sub_x_imm(Reg::X21, Reg::X21, cost as u16);
    }
}

// ============================================================
// Main lowering
// ============================================================

/// Lower an IR function directly (no regalloc2).
///
/// Uses a simple VReg→register mapping with LRU eviction. Values
/// flow through canonical frame slots at control-flow merge points
/// (DefLabel invalidates all mappings, Br stores dirty locals).
pub fn lower_into(
    e: &mut Emitter,
    ir: &IrFunction,
    func_idx: u32,
    body_offsets: &mut [Option<usize>],
    emit_markers: bool,
) -> LowerResult {
    let body_start = e.offset();
    body_offsets[func_idx as usize] = Some(body_start);

    // Count VRegs in the IR.
    let mut max_vreg = 0u32;
    for inst in &ir.insts {
        inst.for_each_def(|v| max_vreg = max_vreg.max(v.0 + 1));
        inst.for_each_use(|v| max_vreg = max_vreg.max(v.0 + 1));
    }

    let mut word_labels: Vec<(usize, String)> = Vec::new();

    let mut regs = RegMap::new(max_vreg, ir.frame_size() as u16);

    // Label tracking.
    let max_label = max_label_index(&ir.insts) + 1;
    let mut label_offsets: Vec<Option<usize>> = vec![None; max_label];
    let mut label_patches: Vec<(Label, PatchPoint)> = Vec::new();

    // Fuel check sites for cold stubs.
    let mut fuel_sites: Vec<FuelCheckSite> = Vec::new();

    let mut pending_cmp: Option<PendingCmp> = None;
    let mut pending_fuel: Option<u32> = None;
    /// After a Call, holds (offset_from_g_lb, prev_fp_value) for the
    /// callee's header. Consumed by the next FuelCheck's cold stub.
    let mut pending_callee_prev_fp: Option<(u16, u32)> = None;
    let mut lr_clobbered = false;

    // Precompute register hints: vregs used as call arg 0 or return
    // value 0 should prefer scratch slot 0 (x9).
    let mut vreg_hint: Vec<Option<u8>> = vec![None; max_vreg as usize];
    for inst in &ir.insts {
        match inst {
            IrInst::Call { args, .. } => {
                if let Some(&(first, _)) = args.first() {
                    vreg_hint[first.0 as usize] = Some(0);
                }
            }
            IrInst::Return { results } => {
                if let Some(&(first, _)) = results.first() {
                    vreg_hint[first.0 as usize] = Some(0);
                }
            }
            _ => {}
        }
    }

    // Precompute last use index for each vreg.
    let mut last_use: Vec<u32> = vec![0; max_vreg as usize];
    for (i, inst) in ir.insts.iter().enumerate() {
        inst.for_each_use(|v| last_use[v.0 as usize] = i as u32);
    }

    // Precompute: for each instruction index, the label of the next
    // DefLabel (for fallthrough elimination).
    let next_label_at: Vec<Option<Label>> = (0..ir.insts.len())
        .map(|i| {
            if i + 1 < ir.insts.len() {
                if let IrInst::DefLabel { label, .. } = &ir.insts[i + 1] {
                    return Some(*label);
                }
            }
            None
        })
        .collect();

    // ---- Prologue ----
    if emit_markers {
        e.mark();
    }
    e.str_x_pre(Reg::X30, Reg::SP, -16);

    // ---- Lower body ----
    for (inst_idx, inst) in ir.insts.iter().enumerate() {
        // Flush pending state BEFORE placing the marker so that
        // flushed code lands in the previous region, not this one.
        let fuses_cmp = matches!(inst, IrInst::BrIfZero { .. } | IrInst::BrIfNonZero { .. });
        if !fuses_cmp {
            flush_pending_cmp(e, &mut pending_cmp);
        }
        let fuses_fuel = matches!(inst, IrInst::FuelCheck { .. });
        if !fuses_fuel {
            flush_pending_fuel(e, &mut pending_fuel);
        }

        let skip_marker = matches!(
            inst,
            IrInst::DefLabel { .. } | IrInst::FuelConsume { .. } | IrInst::FuelCheck { .. }
        );
        if emit_markers && !skip_marker {
            e.mark();
        }

        match inst {
            IrInst::IConst { dst, val } => {
                // Constants default to 8-byte (i64); narrowing happens at use site.
                let reg = { let r = regs.alloc(*dst, vreg_hint[dst.0 as usize], &vreg_hint, inst_idx as u32, &last_use); handle_alloc(e, &mut regs, r) };
                emit_i64_const(e, reg, *val);
                regs.reload_source[dst.0 as usize] = ReloadSource::Const(*val);
            }

            IrInst::ParamDef { dst, idx } => {
                // Value is already in x9+idx from calling convention.
                regs.vreg_size[dst.0 as usize] = ir.local_sizes[*idx as usize];
                let slot_idx = *idx as u8;
                let reg = SCRATCH_REGS[slot_idx as usize];
                if let Some(evicted) = regs.assign(*dst, slot_idx) {
                    handle_eviction(e, &mut regs, evicted, reg);
                }
            }

            IrInst::LocalGet { dst, offset, size } => {
                regs.vreg_size[dst.0 as usize] = *size;
                let reg = { let r = regs.alloc(*dst, vreg_hint[dst.0 as usize], &vreg_hint, inst_idx as u32, &last_use); handle_alloc(e, &mut regs, r) };
                match size {
                    4 => e.ldr_w_uoff(reg, Reg::X29, *offset as u16),
                    8 => e.ldr_x_uoff(reg, Reg::X29, *offset as u16),
                    _ => unreachable!("invalid local size {size}"),
                }
                regs.reload_source[dst.0 as usize] = ReloadSource::Frame {
                    offset: *offset as u16,
                    size: *size,
                };
            }

            IrInst::LocalSet { offset, src, size } => {
                let src_reg = ensure_in_reg(e, &mut regs, *src, ir);
                match size {
                    4 => e.str_w_uoff(src_reg, Reg::X29, *offset as u16),
                    8 => e.str_x_uoff(src_reg, Reg::X29, *offset as u16),
                    _ => unreachable!("invalid local size {size}"),
                }
                // Value is now in frame — safe to evict and reload.
                regs.reload_source[src.0 as usize] = ReloadSource::Frame {
                    offset: *offset as u16,
                    size: *size,
                };
            }

            IrInst::Alu { op, dst, lhs, rhs } => {
                regs.vreg_size[dst.0 as usize] = alu_op_size(*op);
                let lhs_reg = ensure_in_reg(e, &mut regs, *lhs, ir);
                match rhs {
                    Operand::Reg(rhs_vreg) => {
                        let rhs_reg = ensure_in_reg(e, &mut regs, *rhs_vreg, ir);
                        let dst_reg = { let r = regs.alloc(*dst, vreg_hint[dst.0 as usize], &vreg_hint, inst_idx as u32, &last_use); handle_alloc(e, &mut regs, r) };
                        regs.reload_source[dst.0 as usize] = ReloadSource::None;
                        lower_alu_reg(e, *op, dst_reg, lhs_reg, rhs_reg, &mut pending_cmp);
                    }
                    Operand::Imm(imm) => {
                        let dst_reg = { let r = regs.alloc(*dst, vreg_hint[dst.0 as usize], &vreg_hint, inst_idx as u32, &last_use); handle_alloc(e, &mut regs, r) };
                        regs.reload_source[dst.0 as usize] = ReloadSource::None;
                        lower_alu_imm(e, *op, dst_reg, lhs_reg, *imm, &mut pending_cmp);
                    }
                }
            }

            IrInst::Unary { op, dst, src } => {
                regs.vreg_size[dst.0 as usize] = unary_op_size(*op);
                let src_reg = ensure_in_reg(e, &mut regs, *src, ir);
                let dst_reg = { let r = regs.alloc(*dst, vreg_hint[dst.0 as usize], &vreg_hint, inst_idx as u32, &last_use); handle_alloc(e, &mut regs, r) };
                regs.reload_source[dst.0 as usize] = ReloadSource::None;
                lower_unary(e, *op, dst_reg, src_reg);
            }

            IrInst::DefLabel { label, params } => {
                label_offsets[label.0 as usize] = Some(e.offset());
                if !params.is_empty() {
                    // Merge point — all values must come from frame.
                    regs.invalidate_all();
                }
                // Single predecessor (empty params) — register state
                // carries through, no invalidation needed.
                for (i, param) in params.iter().enumerate() {
                    regs.vreg_size[param.0 as usize] = ir.local_sizes[i];
                    regs.reload_source[param.0 as usize] = ReloadSource::Frame {
                        offset: ir.local_byte_offsets[i],
                        size: ir.local_sizes[i],
                    };
                }
            }

            IrInst::Br { label } => {
                regs.invalidate_all();

                // Skip redundant fallthrough branches.
                let is_fallthrough = next_label_at[inst_idx] == Some(*label);
                if !is_fallthrough {
                    emit_branch_to_label(
                        e,
                        *label,
                        &label_offsets,
                        &mut label_patches,
                        |e, off| e.b_offset(off),
                        |e| e.b(),
                    );
                }
            }

            IrInst::BrIfZero { cond, label } => {
                if let Some(cmp) = pending_cmp.take() {
                    let c = cmp.arm_cond.invert();
                    emit_branch_to_label(
                        e,
                        *label,
                        &label_offsets,
                        &mut label_patches,
                        |e, off| e.b_cond_offset(c, off),
                        |e| e.b_cond(c),
                    );
                } else {
                    let rt = ensure_in_reg(e, &mut regs, *cond, ir);
                    emit_branch_to_label(
                        e,
                        *label,
                        &label_offsets,
                        &mut label_patches,
                        |e, off| e.cbz_w_offset(rt, off),
                        |e| e.cbz_w(rt),
                    );
                }
                // Don't invalidate — the not-taken path continues with
                // same register state.
            }

            IrInst::BrIfNonZero { cond, label } => {
                if let Some(cmp) = pending_cmp.take() {
                    let c = cmp.arm_cond;
                    emit_branch_to_label(
                        e,
                        *label,
                        &label_offsets,
                        &mut label_patches,
                        |e, off| e.b_cond_offset(c, off),
                        |e| e.b_cond(c),
                    );
                } else {
                    let rt = ensure_in_reg(e, &mut regs, *cond, ir);
                    emit_branch_to_label(
                        e,
                        *label,
                        &label_offsets,
                        &mut label_patches,
                        |e, off| e.cbnz_w_offset(rt, off),
                        |e| e.cbnz_w(rt),
                    );
                }
            }

            IrInst::FrameStore { offset, src } => {
                let src_reg = ensure_in_reg(e, &mut regs, *src, ir);
                e.str_x_uoff(src_reg, Reg::X29, *offset as u16);
            }

            IrInst::FrameLoad { dst, offset } => {
                let reg = { let r = regs.alloc(*dst, vreg_hint[dst.0 as usize], &vreg_hint, inst_idx as u32, &last_use); handle_alloc(e, &mut regs, r) };
                e.ldr_x_uoff(reg, Reg::X29, *offset as u16);
                regs.reload_source[dst.0 as usize] = ReloadSource::Frame {
                    offset: *offset as u16,
                    size: 8,
                };
            }

            IrInst::Call {
                func_idx: callee_idx,
                args,
                result,
                frame_advance,
                callee_locals_size,
            } => {
                // Move call arguments into x9, x10, ...
                // We need to be careful about conflicts: if arg[i] is
                // already in x(9+j) where j≠i, we might clobber it
                // when moving arg[j].
                //
                // Simple strategy: first collect all arg registers,
                // then move them into position. Use x15 as temp if needed.
                let arg_regs: Vec<(Reg, u8)> = args
                    .iter()
                    .map(|(a, sz)| (ensure_in_reg(e, &mut regs, *a, ir), *sz))
                    .collect();

                // Move args into calling convention registers.
                for (i, &(src, size)) in arg_regs.iter().enumerate() {
                    let dst = Reg(9 + i as u8);
                    if src != dst {
                        mov_sized(e, dst, src, size);
                    }
                }

                regs.invalidate_all();

                let advance = *frame_advance as u16;

                // Stash callee's prev_fp info for the next fuel check's
                // cold stub. prev_fp_offset is only needed on suspend, so
                // we avoid writing it on the hot path entirely.
                let header_off = advance + *callee_locals_size;
                let prev_fp = advance as u32 + *callee_locals_size as u32 + 12
                    - ir.operand_base_offset;
                pending_callee_prev_fp = Some((header_off + 8, prev_fp));

                e.add_x_imm(Reg::X29, Reg::X29, advance);

                let target_word =
                    body_offsets[*callee_idx as usize].unwrap_or(*callee_idx as usize);
                let offset = target_word as i32 - e.offset() as i32;
                e.bl_offset(offset);
                lr_clobbered = true;

                e.sub_x_imm(Reg::X29, Reg::X29, advance);

                // Result is in x9. Map the result VReg to slot 0 (x9).
                // After invalidate_all, slot 0 is empty so no eviction.
                if let Some((r, sz)) = result {
                    regs.vreg_size[r.0 as usize] = *sz;
                    let evicted = regs.assign(*r, 0);
                    debug_assert!(evicted.is_none());
                    regs.reload_source[r.0 as usize] = ReloadSource::None;
                }
            }

            IrInst::Return { results } => {
                // Move results into x9, x10, ...
                for (i, (r, size)) in results.iter().enumerate() {
                    let src = ensure_in_reg(e, &mut regs, *r, ir);
                    let dst = Reg(9 + i as u8);
                    if src != dst {
                        mov_sized(e, dst, src, *size);
                    }
                }

                if lr_clobbered {
                    e.ldr_x_post(Reg::X30, Reg::SP, 16);
                } else {
                    e.add_x_imm(Reg::SP, Reg::SP, 16);
                }
                e.ret();
            }

            IrInst::FuelConsume { cost } => {
                if let Some(prev) = pending_fuel.as_mut() {
                    *prev += cost;
                } else {
                    pending_fuel = Some(*cost);
                }
            }

            IrInst::FuelCheck { resume_pc, .. } => {
                let callee_fp = pending_callee_prev_fp.take();
                if let Some(cost) = pending_fuel.take() {
                    emit_fuel_check_with_cost(e, &mut fuel_sites, cost, *resume_pc, callee_fp);
                } else {
                    emit_fuel_check_sign(e, &mut fuel_sites, *resume_pc, callee_fp);
                }
                lr_clobbered = true;
            }

            IrInst::Trap => {
                e.brk(1);
            }
        }
    }

    flush_pending_cmp(e, &mut pending_cmp);
    flush_pending_fuel(e, &mut pending_fuel);

    // Mark the end of the main body.
    if emit_markers {
        e.mark();
    }

    // ---- Cold fuel-check stubs (per-site) ----
    // Each stub writes this function's own header (func_idx + resume_pc),
    // then returns. For post-call sites, also writes prev_fp_offset into
    // the callee's header (the caller is the only one who knows it).
    //
    // Header layout at [g.lb + locals_size]:
    //   [func_idx(4) | resume_pc(4) | prev_fp_offset(4)]
    let func_idx_offset = ir.operand_base_offset as u16 - 12;
    let resume_pc_offset = ir.operand_base_offset as u16 - 8;
    for site in &fuel_sites {
        let stub = e.offset();

        let fi_label = format!("suspend: func_idx = {func_idx}");
        word_labels.push((e.offset() - body_start, fi_label.clone()));
        emit_i32_const_reg(e, Reg::X0, func_idx as i32);
        word_labels.push((e.offset() - body_start, fi_label));
        e.str_w_uoff(Reg::X0, Reg::X29, func_idx_offset);

        let pc_label = format!("resume_pc = {}", site.resume_pc);
        word_labels.push((e.offset() - body_start, pc_label.clone()));
        emit_i32_const_reg(e, Reg::X0, site.resume_pc as i32);
        word_labels.push((e.offset() - body_start, pc_label));
        e.str_w_uoff(Reg::X0, Reg::X29, resume_pc_offset);

        // Post-call: write callee's prev_fp_offset into the callee's header.
        if let Some((offset, value)) = site.callee_prev_fp {
            let pfp_label = format!("callee prev_fp_offset = {value}");
            word_labels.push((e.offset() - body_start, pfp_label.clone()));
            emit_i32_const_reg(e, Reg::X0, value as i32);
            word_labels.push((e.offset() - body_start, pfp_label));
            e.str_w_uoff(Reg::X0, Reg::X29, offset);
        }

        e.ldr_x_post(Reg::X30, Reg::SP, 16);
        e.ret();
        e.patch_to(site.b_le_patch, stub);
    }

    // Patch forward label branches.
    for (label, pp) in label_patches {
        let target = label_offsets[label.0 as usize]
            .unwrap_or_else(|| panic!("unresolved label L{}", label.0));
        e.patch_to(pp, target);
    }

    let relative_label_offsets: Vec<Option<usize>> = label_offsets
        .iter()
        .map(|off| off.map(|o| o - body_start))
        .collect();

    LowerResult {
        body_start,
        label_offsets: relative_label_offsets,
        word_labels,
    }
}

/// Ensure a VReg is in a physical register, emitting a reload if it
/// was evicted. Returns the physical register.
///
/// If the VReg is not currently mapped, a new register is allocated
/// (possibly evicting another VReg) and the value is reloaded from
/// its `ReloadSource` — either a rematerialized constant, a known
/// frame slot, or a previously spilled slot.
fn ensure_in_reg(e: &mut Emitter, regs: &mut RegMap, vreg: VReg, ir: &IrFunction) -> Reg {
    if let Some(reg) = regs.get(vreg) {
        return reg;
    }
    // VReg was evicted. Allocate a register, handle eviction of the
    // displaced VReg, then reload.
    let r = regs.alloc(vreg, None, &[], u32::MAX, &[]);
    let reg = handle_alloc(e, regs, r);
    match regs.reload_source[vreg.0 as usize] {
        ReloadSource::Const(val) => emit_i64_const(e, reg, val),
        ReloadSource::Frame { offset, size } => match size {
            4 => e.ldr_w_uoff(reg, Reg::X29, offset),
            8 => e.ldr_x_uoff(reg, Reg::X29, offset),
            _ => unreachable!("invalid frame reload size {size}"),
        },
        ReloadSource::Spill { offset } => e.ldr_x_uoff(reg, Reg::X29, offset),
        ReloadSource::None => {
            panic!("VReg v{} has no reload source\n{}", vreg.0, ir);
        }
    }
    reg
}

/// Spill an evicted VReg to a new frame slot if it has no other reload source.
///
/// `evicted_reg` is the physical register that *still holds* the evicted
/// value at the moment this is called (before the new VReg overwrites it).
/// Handle an AllocResult: emit any spill or mov, return the usable register.
fn handle_alloc(e: &mut Emitter, regs: &mut RegMap, result: AllocResult) -> Reg {
    match result {
        AllocResult::Ready(reg) => reg,
        AllocResult::Evicted { reg, evicted } => {
            handle_eviction(e, regs, evicted, reg);
            reg
        }
        AllocResult::Relocated { reg, mov, size } => {
            mov_sized(e, mov.0, mov.1, size);
            reg
        }
    }
}

fn handle_eviction(e: &mut Emitter, regs: &mut RegMap, evicted: VReg, evicted_reg: Reg) {
    match regs.reload_source[evicted.0 as usize] {
        // Already reloadable — no spill needed.
        ReloadSource::Const(_) | ReloadSource::Frame { .. } | ReloadSource::Spill { .. } => {}
        // No reload source — must spill to a new frame slot.
        ReloadSource::None => {
            let offset = regs.next_spill_offset;
            regs.next_spill_offset += 8;
            e.str_x_uoff(evicted_reg, Reg::X29, offset);
            regs.reload_source[evicted.0 as usize] = ReloadSource::Spill { offset };
        }
    }
}

/// Store branch args (locals) to their canonical frame offsets.
///
/// Branch args correspond 1:1 to locals (from `collect_local_args`).
/// We store each arg VReg to its local's frame offset so values are
/// available at the merge point.

// ============================================================
// Branch helpers
// ============================================================

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

pub fn emit_shared_preamble(e: &mut Emitter, func_count: usize) -> SharedHandlerOffsets {
    for _ in 0..func_count {
        e.brk(2);
    }
    let end = e.offset();
    SharedHandlerOffsets { end }
}

pub fn patch_jump_table(e: &mut Emitter, func_idx: u32, target_word: usize) {
    let source = func_idx as usize;
    let word_offset = target_word as i32 - source as i32;
    let imm26 = (word_offset as u32) & 0x03FF_FFFF;
    e.code[source] = 0x14000000 | imm26;
}

// ============================================================
// Fuel check, constants, entry trampoline
// ============================================================

/// A fuel check site in the generated code, with metadata for cold stub emission.
pub struct FuelCheckSite {
    /// Patch point for the conditional branch to the cold stub.
    pub b_le_patch: PatchPoint,
    /// Wasm PC to write as resume_pc in the frame header.
    pub resume_pc: u32,
    /// If this fuel check follows a call, the callee's prev_fp_offset
    /// needs writing on the cold path: (offset_from_g_lb, value).
    pub callee_prev_fp: Option<(u16, u32)>,
}

fn emit_fuel_check_with_cost(
    e: &mut Emitter,
    fuel_sites: &mut Vec<FuelCheckSite>,
    cost: u32,
    resume_pc: u32,
    callee_prev_fp: Option<(u16, u32)>,
) {
    e.subs_x_imm(Reg::X21, Reg::X21, cost as u16);
    let b_le_patch = e.b_cond(Cond::LE);
    fuel_sites.push(FuelCheckSite { b_le_patch, resume_pc, callee_prev_fp });
}

fn emit_fuel_check_sign(
    e: &mut Emitter,
    fuel_sites: &mut Vec<FuelCheckSite>,
    resume_pc: u32,
    callee_prev_fp: Option<(u16, u32)>,
) {
    e.cmp_x_imm(Reg::X21, 0);
    let b_le_patch = e.b_cond(Cond::LT);
    fuel_sites.push(FuelCheckSite { b_le_patch, resume_pc, callee_prev_fp });
}

pub fn emit_entry_trampoline(
    e: &mut Emitter,
    func_body_offset: usize,
    param_offsets: &[u16],
    result_offsets: &[u16],
    locals_header_size: u16,
) -> usize {
    let entry = e.offset();

    e.str_x_pre(Reg::X30, Reg::SP, -16);

    // x29 arrives as wasm_fp.ptr (operand base, past header).
    // Subtract locals_header_size to get g.lb (locals base), so all
    // frame access uses positive unsigned offsets from g.lb.
    //
    //   [params][locals][header][operands...]
    //   ^g.lb                   ^wasm_fp.ptr
    e.sub_x_imm(Reg::X29, Reg::X29, locals_header_size);

    // Load params from canonical local slots into calling convention regs.
    for (i, &off) in param_offsets.iter().enumerate().take(7) {
        let reg = Reg(9 + i as u8);
        e.ldr_w_uoff(reg, Reg::X29, off);
    }

    let offset = func_body_offset as i32 - e.offset() as i32;
    e.bl_offset(offset);

    // Restore x29 to wasm_fp.ptr for result storage and host return.
    e.add_x_imm(Reg::X29, Reg::X29, locals_header_size);

    // Store results from calling convention regs to operand base.
    for (i, &off) in result_offsets.iter().enumerate().take(7) {
        let reg = Reg(9 + i as u8);
        e.str_w_uoff(reg, Reg::X29, off);
    }

    e.ldr_x_post(Reg::X30, Reg::SP, 16);
    e.ret();

    entry
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

/// Width-aware register move: `mov_w` for 4-byte values, `mov_x` for 8-byte.
fn mov_sized(e: &mut Emitter, dst: Reg, src: Reg, size: u8) {
    match size {
        4 => e.mov_w(dst, src),
        _ => e.mov_x(dst, src),
    }
}

/// Result size in bytes for an ALU op: i32 ops → 4, i64 ops → 8.
fn alu_op_size(op: AluOp) -> u8 {
    use AluOp::*;
    match op {
        I32Add | I32Sub | I32Mul | I32DivS | I32DivU | I32RemS | I32RemU |
        I32And | I32Or | I32Xor | I32Shl | I32ShrS | I32ShrU | I32Rotl | I32Rotr |
        I32Eq | I32Ne | I32LtS | I32LtU | I32GtS | I32GtU | I32LeS | I32LeU | I32GeS | I32GeU |
        // i64 comparisons also produce an i32 result (0 or 1)
        I64Eq | I64Ne | I64LtS | I64LtU | I64GtS | I64GtU | I64LeS | I64LeU | I64GeS | I64GeU => 4,
        I64Add | I64Sub | I64Mul | I64DivS | I64DivU | I64RemS | I64RemU |
        I64And | I64Or | I64Xor | I64Shl | I64ShrS | I64ShrU | I64Rotl | I64Rotr => 8,
    }
}

/// Result size in bytes for a unary op.
fn unary_op_size(op: UnaryOp) -> u8 {
    use UnaryOp::*;
    match op {
        I32Clz | I32Ctz | I32Popcnt | I32Eqz |
        I32WrapI64 | I32Extend8S | I32Extend16S |
        I64Eqz => 4,
        I64Clz | I64Ctz | I64Popcnt |
        I64ExtendI32S | I64ExtendI32U |
        I64Extend8S | I64Extend16S | I64Extend32S => 8,
    }
}

fn lower_alu_reg(
    e: &mut Emitter,
    op: AluOp,
    dst: Reg,
    lhs: Reg,
    rhs: Reg,
    pending_cmp: &mut Option<PendingCmp>,
) {
    match op {
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
        AluOp::I32And => e.and_w(dst, lhs, rhs),
        AluOp::I32Or => e.orr_w(dst, lhs, rhs),
        AluOp::I32Xor => e.eor_w(dst, lhs, rhs),
        AluOp::I32Shl => e.lsl_w(dst, lhs, rhs),
        AluOp::I32ShrS => e.asr_w(dst, lhs, rhs),
        AluOp::I32ShrU => e.lsr_w(dst, lhs, rhs),
        AluOp::I32Rotl => e.ror_w(dst, lhs, rhs),
        AluOp::I32Rotr => e.ror_w(dst, lhs, rhs),
        AluOp::I32Eq
        | AluOp::I32Ne
        | AluOp::I32LtS
        | AluOp::I32LtU
        | AluOp::I32GtS
        | AluOp::I32GtU
        | AluOp::I32LeS
        | AluOp::I32LeU
        | AluOp::I32GeS
        | AluOp::I32GeU => {
            e.cmp_w_reg(lhs, rhs);
            let arm_cond = alu_op_to_cond(op);
            *pending_cmp = Some(PendingCmp {
                arm_cond,
                dst_reg: dst,
            });
        }
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
        AluOp::I64And => e.and_x(dst, lhs, rhs),
        AluOp::I64Or => e.orr_x(dst, lhs, rhs),
        AluOp::I64Xor => e.eor_x(dst, lhs, rhs),
        AluOp::I64Shl => e.lsl_x(dst, lhs, rhs),
        AluOp::I64ShrS => e.asr_x(dst, lhs, rhs),
        AluOp::I64ShrU => e.lsr_x(dst, lhs, rhs),
        AluOp::I64Rotl => e.ror_x(dst, lhs, rhs),
        AluOp::I64Rotr => e.ror_x(dst, lhs, rhs),
        AluOp::I64Eq
        | AluOp::I64Ne
        | AluOp::I64LtS
        | AluOp::I64LtU
        | AluOp::I64GtS
        | AluOp::I64GtU
        | AluOp::I64LeS
        | AluOp::I64LeU
        | AluOp::I64GeS
        | AluOp::I64GeU => {
            e.cmp_x_reg(lhs, rhs);
            let arm_cond = alu_op_to_cond(op);
            *pending_cmp = Some(PendingCmp {
                arm_cond,
                dst_reg: dst,
            });
        }
    }
}

fn lower_alu_imm(
    e: &mut Emitter,
    op: AluOp,
    dst: Reg,
    lhs: Reg,
    imm: i64,
    pending_cmp: &mut Option<PendingCmp>,
) {
    let is_cmp = matches!(
        op,
        AluOp::I32Eq
            | AluOp::I32Ne
            | AluOp::I32LtS
            | AluOp::I32LtU
            | AluOp::I32GtS
            | AluOp::I32GtU
            | AluOp::I32LeS
            | AluOp::I32LeU
            | AluOp::I32GeS
            | AluOp::I32GeU
            | AluOp::I64Eq
            | AluOp::I64Ne
            | AluOp::I64LtS
            | AluOp::I64LtU
            | AluOp::I64GtS
            | AluOp::I64GtU
            | AluOp::I64LeS
            | AluOp::I64LeU
            | AluOp::I64GeS
            | AluOp::I64GeU
    );
    if is_cmp {
        let is_64 = matches!(
            op,
            AluOp::I64Eq
                | AluOp::I64Ne
                | AluOp::I64LtS
                | AluOp::I64LtU
                | AluOp::I64GtS
                | AluOp::I64GtU
                | AluOp::I64LeS
                | AluOp::I64LeU
                | AluOp::I64GeS
                | AluOp::I64GeU
        );
        if is_64 {
            e.cmp_x_imm(lhs, imm as u16);
        } else {
            e.cmp_w_imm(lhs, imm as u16);
        }
        let arm_cond = alu_op_to_cond(op);
        *pending_cmp = Some(PendingCmp {
            arm_cond,
            dst_reg: dst,
        });
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

/// Find the maximum label index used in the IR instructions.
fn max_label_index(insts: &[IrInst]) -> usize {
    let mut max = 0usize;
    for inst in insts {
        match inst {
            IrInst::DefLabel { label, .. }
            | IrInst::Br { label, .. }
            | IrInst::BrIfZero { label, .. }
            | IrInst::BrIfNonZero { label, .. } => {
                max = max.max(label.0 as usize);
            }
            _ => {}
        }
    }
    max
}
