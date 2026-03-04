use crate::emit::{Cond, Emitter, PatchPoint, Reg};
use crate::ir::{AluOp, IrFunction, IrInst, Label, Operand, UnaryOp, VReg};

/// Physical scratch registers available for allocation (x9–x15).
const SCRATCH_REGS: [Reg; 7] = [
    Reg(9), Reg(10), Reg(11), Reg(12), Reg(13), Reg(14), Reg(15),
];

/// Result of lowering a single function.
pub struct LowerResult {
    /// Word offset where the function's code starts.
    pub body_start: usize,
    /// Label index → word offset relative to `body_start`.
    pub label_offsets: Vec<Option<usize>>,
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
    /// Reload from a known frame slot: `[x29 + offset]` with the given width.
    Frame { offset: u16, size: u8 },
    /// Was spilled to a dynamically allocated frame slot during eviction.
    Spill { offset: u16 },
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
    /// Next available spill slot offset from x29 (grows upward from frame_size).
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

    /// Allocate a register for a VReg.
    ///
    /// Returns `(reg, evicted_vreg)`. When eviction occurs, the evicted
    /// VReg's value is still in `reg` at the moment this returns — the
    /// caller must call `handle_eviction` before writing to `reg`.
    fn alloc(&mut self, vreg: VReg) -> (Reg, Option<VReg>) {
        // Already mapped?
        if let Some(idx) = self.vreg_to_idx[vreg.0 as usize] {
            self.use_tick += 1;
            self.slot_tick[idx as usize] = self.use_tick;
            return (SCRATCH_REGS[idx as usize], None);
        }
        // Find a free slot.
        for i in 0..7u8 {
            if self.slot_vreg[i as usize].is_none() {
                self.assign(vreg, i);
                return (SCRATCH_REGS[i as usize], None);
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
        (SCRATCH_REGS[best_idx as usize], evicted)
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

    let mut regs = RegMap::new(max_vreg, ir.frame_size() as u16);

    // Label tracking.
    let max_label = max_label_index(&ir.insts) + 1;
    let mut label_offsets: Vec<Option<usize>> = vec![None; max_label];
    let mut label_patches: Vec<(Label, PatchPoint)> = Vec::new();

    // Fuel check sites for cold stubs.
    let mut fuel_sites: Vec<FuelCheckSite> = Vec::new();

    let mut pending_cmp: Option<PendingCmp> = None;
    let mut pending_fuel: Option<u32> = None;
    let mut lr_clobbered = false;

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
        if emit_markers && !matches!(inst, IrInst::DefLabel { .. }) {
            e.mark();
        }

        // Flush pending cmp unless this instruction fuses with it.
        let fuses_cmp = matches!(
            inst,
            IrInst::BrIfZero { .. } | IrInst::BrIfNonZero { .. }
        );
        if !fuses_cmp {
            flush_pending_cmp(e, &mut pending_cmp);
        }

        // Flush pending fuel unless this is a FuelCheck (fuses).
        let fuses_fuel = matches!(inst, IrInst::FuelCheck { .. });
        if !fuses_fuel {
            flush_pending_fuel(e, &mut pending_fuel);
        }

        match inst {
            IrInst::IConst { dst, val } => {
                let (reg, evicted) = regs.alloc(*dst);
                handle_eviction(e, &mut regs, evicted, reg);
                emit_i64_const(e, reg, *val);
                regs.reload_source[dst.0 as usize] = ReloadSource::Const(*val);
            }

            IrInst::ParamDef { dst, idx } => {
                // Value is already in x9+idx from calling convention.
                let slot_idx = *idx as u8;
                let reg = SCRATCH_REGS[slot_idx as usize];
                let evicted = regs.assign(*dst, slot_idx);
                handle_eviction(e, &mut regs, evicted, reg);
            }

            IrInst::LocalGet { dst, offset, size } => {
                let (reg, evicted) = regs.alloc(*dst);
                handle_eviction(e, &mut regs, evicted, reg);
                match size {
                    4 => e.ldr_w_uoff(reg, Reg::X29, *offset as u16),
                    8 => e.ldr_x_uoff(reg, Reg::X29, *offset as u16),
                    _ => unreachable!("invalid local size {size}"),
                }
                regs.reload_source[dst.0 as usize] =
                    ReloadSource::Frame { offset: *offset as u16, size: *size };
            }

            IrInst::LocalSet { offset, src, size } => {
                let src_reg = ensure_in_reg(e, &mut regs, *src, ir);
                match size {
                    4 => e.str_w_uoff(src_reg, Reg::X29, *offset as u16),
                    8 => e.str_x_uoff(src_reg, Reg::X29, *offset as u16),
                    _ => unreachable!("invalid local size {size}"),
                }
            }

            IrInst::Alu { op, dst, lhs, rhs } => {
                let lhs_reg = ensure_in_reg(e, &mut regs, *lhs, ir);
                match rhs {
                    Operand::Reg(rhs_vreg) => {
                        let rhs_reg = ensure_in_reg(e, &mut regs, *rhs_vreg, ir);
                        let (dst_reg, evicted) = regs.alloc(*dst);
                        handle_eviction(e, &mut regs, evicted, dst_reg);
                        // Alu results have no natural reload source; they will
                        // be spilled on eviction.
                        regs.reload_source[dst.0 as usize] = ReloadSource::None;
                        lower_alu_reg(e, *op, dst_reg, lhs_reg, rhs_reg, &mut pending_cmp);
                    }
                    Operand::Imm(imm) => {
                        let (dst_reg, evicted) = regs.alloc(*dst);
                        handle_eviction(e, &mut regs, evicted, dst_reg);
                        regs.reload_source[dst.0 as usize] = ReloadSource::None;
                        lower_alu_imm(e, *op, dst_reg, lhs_reg, *imm, &mut pending_cmp);
                    }
                }
            }

            IrInst::Unary { op, dst, src } => {
                let src_reg = ensure_in_reg(e, &mut regs, *src, ir);
                let (dst_reg, evicted) = regs.alloc(*dst);
                handle_eviction(e, &mut regs, evicted, dst_reg);
                regs.reload_source[dst.0 as usize] = ReloadSource::None;
                lower_unary(e, *op, dst_reg, src_reg);
            }

            IrInst::DefLabel { label, params } => {
                // At merge points, all values must come from frame.
                // Invalidate register mappings.
                regs.invalidate_all();
                label_offsets[label.0 as usize] = Some(e.offset());
                // Set reload sources for block params — they correspond
                // 1:1 to locals stored by store_branch_args.
                for (i, param) in params.iter().enumerate() {
                    regs.reload_source[param.0 as usize] =
                        ReloadSource::Frame {
                            offset: ir.local_byte_offsets[i],
                            size: ir.local_sizes[i],
                        };
                }
            }

            IrInst::Br { label, args } => {
                // Store branch args (locals) to their canonical frame
                // offsets so they're available at the merge point.
                store_branch_args(e, &mut regs, args, ir);
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

            IrInst::BrIfZero { cond, label, args } => {
                if let Some(cmp) = pending_cmp.take() {
                    // Fused compare-and-branch: cmp already emitted,
                    // branch if condition was false (zero).
                    store_branch_args(e, &mut regs, args, ir);
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
                    store_branch_args(e, &mut regs, args, ir);
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

            IrInst::BrIfNonZero { cond, label, args } => {
                if let Some(cmp) = pending_cmp.take() {
                    store_branch_args(e, &mut regs, args, ir);
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
                    store_branch_args(e, &mut regs, args, ir);
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
                let (reg, evicted) = regs.alloc(*dst);
                handle_eviction(e, &mut regs, evicted, reg);
                e.ldr_x_uoff(reg, Reg::X29, *offset as u16);
                regs.reload_source[dst.0 as usize] =
                    ReloadSource::Frame { offset: *offset as u16, size: 8 };
            }

            IrInst::Call {
                func_idx: callee_idx,
                args,
                result,
                frame_advance,
            } => {
                // Move call arguments into x9, x10, ...
                // We need to be careful about conflicts: if arg[i] is
                // already in x(9+j) where j≠i, we might clobber it
                // when moving arg[j].
                //
                // Simple strategy: first collect all arg registers,
                // then move them into position. Use x15 as temp if needed.
                let arg_regs: Vec<Reg> = args
                    .iter()
                    .map(|a| ensure_in_reg(e, &mut regs, *a, ir))
                    .collect();

                // Move args into calling convention registers.
                for (i, &src) in arg_regs.iter().enumerate() {
                    let dst = Reg(9 + i as u8);
                    if src != dst {
                        e.mov_x(dst, src);
                    }
                }

                regs.invalidate_all();

                let advance = *frame_advance as u16;
                e.add_x_imm(Reg::X29, Reg::X29, advance);

                let target_word =
                    body_offsets[*callee_idx as usize].unwrap_or(*callee_idx as usize);
                let offset = target_word as i32 - e.offset() as i32;
                e.bl_offset(offset);
                lr_clobbered = true;

                e.sub_x_imm(Reg::X29, Reg::X29, advance);

                // Result is in x9. Map the result VReg to slot 0 (x9).
                // After invalidate_all, slot 0 is empty so no eviction.
                if let Some(r) = result {
                    let evicted = regs.assign(*r, 0);
                    debug_assert!(evicted.is_none());
                    regs.reload_source[r.0 as usize] = ReloadSource::None;
                }
            }

            IrInst::Return { results } => {
                // Move results into x9, x10, ...
                for (i, r) in results.iter().enumerate() {
                    let src = ensure_in_reg(e, &mut regs, *r, ir);
                    let dst = Reg(9 + i as u8);
                    if src != dst {
                        e.mov_x(dst, src);
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

            IrInst::FuelCheck { .. } => {
                if let Some(cost) = pending_fuel.take() {
                    emit_fuel_check_with_cost(e, &mut fuel_sites, cost);
                } else {
                    emit_fuel_check_sign(e, &mut fuel_sites);
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

    // ---- Cold fuel-check stubs ----
    let suspend_handler = e.offset();
    e.brk(0xDEAD);
    e.movz_x(Reg::X9, 1);
    e.str_x_uoff(Reg::X9, Reg::X20, 0);
    e.ldr_x_uoff(Reg::X9, Reg::X20, 8);
    e.ldur_x(Reg::X30, Reg::X9, -16);
    e.mov_sp_from(Reg::X28);
    e.ret();

    for site in &fuel_sites {
        e.patch_to(site.b_le_patch, suspend_handler);
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
    let (reg, evicted) = regs.alloc(vreg);
    handle_eviction(e, regs, evicted, reg);
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
fn handle_eviction(
    e: &mut Emitter,
    regs: &mut RegMap,
    evicted: Option<VReg>,
    evicted_reg: Reg,
) {
    let ev = match evicted {
        Some(v) => v,
        None => return,
    };
    match regs.reload_source[ev.0 as usize] {
        // Already reloadable — no spill needed.
        ReloadSource::Const(_) | ReloadSource::Frame { .. } | ReloadSource::Spill { .. } => {}
        // No reload source — must spill to a new frame slot.
        ReloadSource::None => {
            let offset = regs.next_spill_offset;
            regs.next_spill_offset += 8;
            e.str_x_uoff(evicted_reg, Reg::X29, offset);
            regs.reload_source[ev.0 as usize] = ReloadSource::Spill { offset };
        }
    }
}

/// Store branch args (locals) to their canonical frame offsets.
///
/// Branch args correspond 1:1 to locals (from `collect_local_args`).
/// We store each arg VReg to its local's frame offset so values are
/// available at the merge point.
fn store_branch_args(e: &mut Emitter, regs: &mut RegMap, args: &[VReg], ir: &IrFunction) {
    for (i, arg) in args.iter().enumerate() {
        if let Some(reg) = regs.get(*arg) {
            let offset = ir.local_byte_offsets[i];
            let size = ir.local_sizes[i];
            match size {
                4 => e.str_w_uoff(reg, Reg::X29, offset),
                8 => e.str_x_uoff(reg, Reg::X29, offset),
                _ => unreachable!("invalid local size {size}"),
            }
        }
        // If arg VReg is not in a register, it was already stored
        // to frame (e.g., by a prior LocalSet or was never loaded).
    }
}

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

struct FuelCheckSite {
    b_le_patch: PatchPoint,
}

fn emit_fuel_check_with_cost(e: &mut Emitter, fuel_sites: &mut Vec<FuelCheckSite>, cost: u32) {
    e.subs_x_imm(Reg::X21, Reg::X21, cost as u16);
    let b_le_patch = e.b_cond(Cond::LE);
    fuel_sites.push(FuelCheckSite { b_le_patch });
}

fn emit_fuel_check_sign(e: &mut Emitter, fuel_sites: &mut Vec<FuelCheckSite>) {
    e.cmp_x_imm(Reg::X21, 0);
    let b_le_patch = e.b_cond(Cond::LT);
    fuel_sites.push(FuelCheckSite { b_le_patch });
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
    e.sub_x_imm(Reg::X29, Reg::X29, locals_header_size);

    for (i, &off) in param_offsets.iter().enumerate().take(7) {
        let reg = Reg(9 + i as u8);
        e.ldr_w_uoff(reg, Reg::X29, off);
    }

    let offset = func_body_offset as i32 - e.offset() as i32;
    e.bl_offset(offset);

    e.add_x_imm(Reg::X29, Reg::X29, locals_header_size);

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
        AluOp::I32Eq | AluOp::I32Ne | AluOp::I32LtS | AluOp::I32LtU
        | AluOp::I32GtS | AluOp::I32GtU | AluOp::I32LeS | AluOp::I32LeU
        | AluOp::I32GeS | AluOp::I32GeU => {
            e.cmp_w_reg(lhs, rhs);
            let arm_cond = alu_op_to_cond(op);
            *pending_cmp = Some(PendingCmp { arm_cond, dst_reg: dst });
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
        AluOp::I64Eq | AluOp::I64Ne | AluOp::I64LtS | AluOp::I64LtU
        | AluOp::I64GtS | AluOp::I64GtU | AluOp::I64LeS | AluOp::I64LeU
        | AluOp::I64GeS | AluOp::I64GeU => {
            e.cmp_x_reg(lhs, rhs);
            let arm_cond = alu_op_to_cond(op);
            *pending_cmp = Some(PendingCmp { arm_cond, dst_reg: dst });
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
        AluOp::I32Eq | AluOp::I32Ne | AluOp::I32LtS | AluOp::I32LtU
        | AluOp::I32GtS | AluOp::I32GtU | AluOp::I32LeS | AluOp::I32LeU
        | AluOp::I32GeS | AluOp::I32GeU
        | AluOp::I64Eq | AluOp::I64Ne | AluOp::I64LtS | AluOp::I64LtU
        | AluOp::I64GtS | AluOp::I64GtU | AluOp::I64LeS | AluOp::I64LeU
        | AluOp::I64GeS | AluOp::I64GeU
    );
    if is_cmp {
        let is_64 = matches!(
            op,
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
