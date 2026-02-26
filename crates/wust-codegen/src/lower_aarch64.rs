use crate::code_buffer::CodeBuffer;
use crate::context::JitContext;
use crate::emit::{Cond, Emitter, PatchPoint, Reg};
use crate::ir::{IrCond, IrFunction, IrInst, Label, VReg};

/// Compiled JIT code for a single function (standalone mode).
pub struct CompiledFunction {
    pub buffer: CodeBuffer,
    /// Instruction words (snapshot from emitter, readable after finalize).
    pub code: Vec<u32>,
    /// Byte offset of the completion handler within the code buffer.
    pub completion_offset: usize,
    /// Word offsets marking boundaries between logical regions.
    /// Marker 0 = prologue, markers 1..N+1 = IR instructions 0..N,
    /// then yield handler, completion handler.
    pub markers: Vec<usize>,
}

impl CompiledFunction {
    /// Entry point to the compiled code.
    pub fn entry(&self) -> *const u8 {
        self.buffer.entry()
    }

    /// Address of the completion handler (used as lr for fiber entry).
    pub fn completion_handler(&self) -> *const u8 {
        unsafe { self.buffer.entry().add(self.completion_offset) }
    }
}

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

/// How calls are emitted — differs between standalone and shared-buffer modes.
#[allow(dead_code)]
enum CallMode<'a> {
    /// Standalone mode: indirect call via func_table in context.
    Indirect,
    /// Shared-buffer mode: PC-relative call through jump table.
    PcRelative {
        shared: &'a SharedHandlerOffsets,
        /// For each func_idx, `Some(word_offset)` if its body has been
        /// compiled already (enables direct BL instead of jump table hop).
        body_offsets: &'a [Option<usize>],
    },
}

/// Physical register pool for virtual register allocation.
///
/// We use x9–x15 (7 registers) as the allocatable pool. These are
/// caller-saved scratch registers on aarch64, which means we must
/// spill them before calls.
const PHYS_REGS: [Reg; 7] = [
    Reg::X9,
    Reg::X10,
    Reg(11),
    Reg(12),
    Reg(13),
    Reg(14),
    Reg(15),
];

/// Maps VReg → physical register assignment.
struct RegAlloc {
    /// For each VReg index, the assigned physical register (or None if spilled/unassigned).
    assignments: Vec<Option<Reg>>,
    /// For each physical register index in PHYS_REGS, whether it's free.
    free: [bool; 7],
    /// Last-use position for each VReg (instruction index where it's used last).
    last_use: Vec<usize>,
}

impl RegAlloc {
    fn new(vreg_count: u32, last_use: Vec<usize>) -> Self {
        RegAlloc {
            assignments: vec![None; vreg_count as usize],
            free: [true; 7],
            last_use,
        }
    }

    /// Allocate a physical register for a VReg.
    fn alloc(&mut self, vreg: VReg) -> Reg {
        for (i, &is_free) in self.free.iter().enumerate() {
            if is_free {
                self.free[i] = false;
                self.assignments[vreg.0 as usize] = Some(PHYS_REGS[i]);
                return PHYS_REGS[i];
            }
        }
        panic!(
            "register allocator exhausted: no free physical register for v{}",
            vreg.0
        );
    }

    /// Get the physical register assigned to a VReg.
    fn get(&self, vreg: VReg) -> Reg {
        self.assignments[vreg.0 as usize]
            .unwrap_or_else(|| panic!("v{} has no physical register assigned", vreg.0))
    }

    /// Try to get the physical register for a VReg, returning None if unassigned.
    fn try_get(&self, vreg: VReg) -> Option<Reg> {
        self.assignments[vreg.0 as usize]
    }

    /// Free the physical register for a VReg if this is its last use.
    fn maybe_free(&mut self, vreg: VReg, inst_idx: usize) {
        if self.last_use[vreg.0 as usize] == inst_idx {
            if let Some(phys) = self.assignments[vreg.0 as usize] {
                for (i, &r) in PHYS_REGS.iter().enumerate() {
                    if r == phys {
                        self.free[i] = true;
                        break;
                    }
                }
                self.assignments[vreg.0 as usize] = None;
            }
        }
    }

    /// Free all currently-allocated physical registers (used before calls).
    fn free_all(&mut self) {
        self.free = [true; 7];
        // Note: assignments stay so we can look up post-call, but the
        // registers are considered dead after a call. The VRegs defined
        // before a call should have been consumed or spilled.
    }
}

/// Tracks known constant values for VRegs (lazy constant materialization).
///
/// When an `IConst` instruction is encountered, we record its value here
/// instead of immediately emitting a `mov`. When a consuming instruction
/// can fold the constant as an immediate operand (e.g., `sub w, w, #imm`),
/// we use the immediate encoding directly. Otherwise we materialize the
/// constant into a physical register on demand.
struct VRegConsts {
    /// For each VReg index, the known constant value (if from IConst).
    values: Vec<Option<i64>>,
}

impl VRegConsts {
    fn new(vreg_count: u32) -> Self {
        VRegConsts {
            values: vec![None; vreg_count as usize],
        }
    }

    /// Record a constant value for a VReg.
    fn set(&mut self, vreg: VReg, val: i64) {
        self.values[vreg.0 as usize] = Some(val);
    }

    /// Get the known constant value for a VReg, if any.
    fn get(&self, vreg: VReg) -> Option<i64> {
        self.values[vreg.0 as usize]
    }

    /// Check if a VReg is a small unsigned constant that fits in imm12 (0..4095).
    fn as_u12(&self, vreg: VReg) -> Option<u16> {
        self.get(vreg).and_then(|v| {
            if v >= 0 && v <= 4095 {
                Some(v as u16)
            } else {
                None
            }
        })
    }
}

/// Tracks which physical registers currently hold local values.
///
/// Avoids redundant loads from the frame when a register already
/// contains the local's current value — e.g., after a prologue store
/// or a `LocalSet`, the subsequent `LocalGet` can reuse the register.
struct LocalCache {
    /// For each local index, the physical register holding its value.
    entries: Vec<Option<Reg>>,
}

impl LocalCache {
    fn new(total_locals: usize) -> Self {
        LocalCache {
            entries: vec![None; total_locals],
        }
    }

    /// Record that `reg` holds the current value of `local_idx`.
    fn set(&mut self, local_idx: usize, reg: Reg) {
        if local_idx < self.entries.len() {
            self.entries[local_idx] = Some(reg);
        }
    }

    /// Get the cached register for a local, if any.
    fn get(&self, local_idx: usize) -> Option<Reg> {
        self.entries.get(local_idx).copied().flatten()
    }

    /// Invalidate all entries (e.g., after a call or at a label).
    fn clear(&mut self) {
        self.entries.fill(None);
    }

    /// Invalidate any entry pointing to `reg` (called when a register is freed).
    fn invalidate_reg(&mut self, reg: Reg) {
        for entry in &mut self.entries {
            if *entry == Some(reg) {
                *entry = None;
            }
        }
    }
}

/// Ensure a VReg has a physical register, materializing a constant if needed.
///
/// If the VReg was defined by IConst and hasn't been allocated yet, this
/// allocates a physical register and emits the constant load. Returns the
/// physical register.
fn materialize(e: &mut Emitter, ra: &mut RegAlloc, consts: &VRegConsts, vreg: VReg) -> Reg {
    if let Some(_) = ra.try_get(vreg) {
        return ra.get(vreg);
    }
    // VReg has no physical register — must be a lazy constant.
    let val = consts
        .get(vreg)
        .unwrap_or_else(|| panic!("v{} has no physical register and no known constant", vreg.0));
    let phys = ra.alloc(vreg);
    emit_i64_const(e, phys, val);
    phys
}

/// Free a VReg if it's at its last use, and invalidate any local cache
/// entries pointing to the freed register.
fn maybe_free_with_cache(
    ra: &mut RegAlloc,
    local_cache: &mut LocalCache,
    vreg: VReg,
    inst_idx: usize,
) {
    if ra.last_use[vreg.0 as usize] == inst_idx {
        if let Some(phys) = ra.try_get(vreg) {
            local_cache.invalidate_reg(phys);
        }
        ra.maybe_free(vreg, inst_idx);
    }
}

/// Compute last-use position for each VReg by scanning instructions backward.
fn compute_last_use(insts: &[IrInst], vreg_count: u32) -> Vec<usize> {
    let mut last_use = vec![0usize; vreg_count as usize];
    for (i, inst) in insts.iter().enumerate() {
        for_each_use(inst, |vreg| {
            last_use[vreg.0 as usize] = i;
        });
    }
    last_use
}

/// Call `f` for every VReg that is *read* by `inst`.
fn for_each_use(inst: &IrInst, mut f: impl FnMut(VReg)) {
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
        IrInst::FuelCheck => {}
        IrInst::Trap => {}
    }
}

const CTX_FUNC_TABLE: u16 = std::mem::offset_of!(JitContext, func_table) as u16;
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

/// Lower an IR function to native aarch64 machine code.
///
/// Register convention:
/// - x20: context pointer (→ JitContext)
/// - x21: fuel counter
/// - x29: locals base pointer (wasm frame pointer)
/// - x30: link register
/// - x9–x15: allocatable scratch registers for virtual regs
/// - x0: temp for yield handler (outside VReg pool)
pub fn lower(ir: &IrFunction) -> Result<CompiledFunction, anyhow::Error> {
    let mut e = Emitter::new();
    let mut fuel_sites: Vec<FuelCheckSite> = Vec::new();

    // Count VRegs for register allocation.
    let vreg_count = count_vregs(&ir.insts);
    let last_use = compute_last_use(&ir.insts, vreg_count);
    let mut ra = RegAlloc::new(vreg_count, last_use);

    // Track label positions and pending patches.
    let max_label = count_labels(&ir.insts);
    let mut label_offsets: Vec<Option<usize>> = vec![None; max_label as usize];
    let mut label_patches: Vec<(Label, PatchPoint)> = Vec::new();

    // ---- Prologue ----
    e.mark();
    // TODO: pointer authentication (pacibz / autibz) — disabled for now.
    // e.code.push(0xD503235F); // pacibz

    // Save return address (x29 is the wasm frame pointer, managed by caller).
    e.str_x_pre(Reg::X30, Reg::SP, -16);

    // Copy params from registers (x9, x10, ...) to local slots.
    for i in 0..ir.param_count {
        let src = Reg(9 + i as u8);
        e.str_x_uoff(src, Reg::X29, (i as u16) * 8);
    }

    // Zero-initialize extra locals (beyond params).
    let extra_locals = ir.total_local_count - ir.param_count;
    for i in 0..extra_locals {
        let offset = ((ir.param_count + i) as u16) * 8;
        e.str_x_uoff(Reg::XZR, Reg::X29, offset);
    }

    // Seed local cache: params are in registers after prologue stores.
    let mut local_cache = LocalCache::new(ir.total_local_count as usize);
    for i in 0..ir.param_count {
        local_cache.set(i as usize, Reg(9 + i as u8));
    }

    // ---- Lower each IR instruction ----
    lower_body(
        &mut e,
        ir,
        &mut ra,
        &mut fuel_sites,
        &mut label_offsets,
        &mut label_patches,
        &CallMode::Indirect,
        &mut local_cache,
        true, // emit markers
    );

    // ---- Cold fuel-check stubs ----
    //
    // Each fuel check in the hot path is just `subs; b.le`. When fuel
    // runs out, it branches here. The stub does `bl yield_handler`
    // (which sets x30 = resume point for fiber mode) then jumps back.
    e.mark();
    let mut yield_bl_patches: Vec<PatchPoint> = Vec::new();
    for site in &fuel_sites {
        e.patch(site.b_le_patch);
        let bl_pp = e.bl(); // bl yield_handler (sets x30 for fiber resume)
        yield_bl_patches.push(bl_pp);
        // Branch back to resume point (instruction after the b.le).
        let current = e.offset();
        let offset = site.resume_offset as i32 - current as i32;
        e.b_offset(offset);
    }

    // ---- Yield handler (cold path) ----
    e.mark();
    let yield_target = e.offset();

    // Check is_fiber flag in context (use x0 as temp, outside VReg pool).
    e.ldr_x_uoff(Reg::X0, Reg::X20, CTX_IS_FIBER);
    let fiber_branch = e.cbnz_x(Reg::X0);

    // Non-fiber path: simple unwind.
    emit_i32_const_reg(&mut e, Reg::W0, -1);
    e.ldr_x_post(Reg::X30, Reg::SP, 16);
    e.ret();

    // Fiber yield path.
    e.patch(fiber_branch);
    emit_fiber_yield(&mut e);

    // ---- Completion handler (fiber mode only) ----
    e.mark();
    let completion_offset = e.offset();
    emit_fiber_complete(&mut e);

    // Patch cold-stub BLs to yield handler.
    for pp in yield_bl_patches {
        e.patch_to(pp, yield_target);
    }

    // Patch forward label branches.
    for (label, pp) in label_patches {
        let target = label_offsets[label.0 as usize]
            .unwrap_or_else(|| panic!("unresolved label L{}", label.0));
        e.patch_to(pp, target);
    }

    // ---- Finalize ----
    let completion_byte_offset = completion_offset * 4;
    let code = e.code().to_vec();
    let mut buffer = CodeBuffer::new(code.len() * 4 + 64)?;
    for &word in &code {
        buffer.emit_u32(word);
    }
    buffer.finalize()?;

    Ok(CompiledFunction {
        buffer,
        code,
        completion_offset: completion_byte_offset,
        markers: e.markers,
    })
}

/// Shared lowering loop for IR instructions.
///
/// Handles all IR instructions with peephole optimizations:
/// - Lazy constant materialization (IConst values tracked, folded into immediates)
/// - Immediate folding for Add, Sub, Cmp when RHS is a small constant (0..4095)
/// - Fused compare-and-branch (Cmp + BrIfZero/BrIfNonZero → cmp + b.cond)
///
/// The `call_mode` parameter controls how function calls are emitted:
/// - `Indirect`: loads target from func_table in context (standalone mode)
/// - `PcRelative`: emits bl to jump table entry (shared buffer mode)
fn lower_body(
    e: &mut Emitter,
    ir: &IrFunction,
    ra: &mut RegAlloc,
    fuel_sites: &mut Vec<FuelCheckSite>,
    label_offsets: &mut [Option<usize>],
    label_patches: &mut Vec<(Label, PatchPoint)>,
    call_mode: &CallMode,
    local_cache: &mut LocalCache,
    emit_markers: bool,
) {
    let result_count = ir.result_count as usize;

    let vreg_count = count_vregs(&ir.insts);
    let mut consts = VRegConsts::new(vreg_count);

    let insts = &ir.insts;
    let mut inst_idx = 0;
    while inst_idx < insts.len() {
        let inst = &insts[inst_idx];
        if emit_markers {
            e.mark();
        }

        match inst {
            IrInst::IConst { dst, val } => {
                // Lazy: record the constant, don't emit code yet.
                consts.set(*dst, *val);
                // Still need to track in regalloc's last_use for freeing.
                // But don't allocate a physical register — that happens
                // on demand in materialize().
            }

            IrInst::LocalGet { dst, idx } => {
                if let Some(cached_reg) = local_cache.get(*idx as usize) {
                    // Cache hit: the register still holds the local's value.
                    let phys = ra.alloc(*dst);
                    if phys != cached_reg {
                        e.mov_x(phys, cached_reg);
                    }
                    local_cache.set(*idx as usize, phys);
                } else {
                    // Cache miss: load from frame.
                    let phys = ra.alloc(*dst);
                    let offset = (*idx as u16) * 8;
                    e.ldr_x_uoff(phys, Reg::X29, offset);
                    local_cache.set(*idx as usize, phys);
                }
            }

            IrInst::LocalSet { idx, src } => {
                let phys_src = materialize(e, ra, &consts, *src);
                let offset = (*idx as u16) * 8;
                e.str_x_uoff(phys_src, Reg::X29, offset);
                local_cache.set(*idx as usize, phys_src);
                maybe_free_with_cache(ra, local_cache, *src, inst_idx);
            }

            IrInst::Add { dst, lhs, rhs } => {
                // Try immediate folding: add wd, wn, #imm
                if let Some(imm) = consts.as_u12(*rhs) {
                    let phys_lhs = materialize(e, ra, &consts, *lhs);
                    maybe_free_with_cache(ra, local_cache, *lhs, inst_idx);
                    maybe_free_with_cache(ra, local_cache, *rhs, inst_idx);
                    let phys_dst = ra.alloc(*dst);
                    e.add_w_imm(phys_dst, phys_lhs, imm);
                } else {
                    let phys_lhs = materialize(e, ra, &consts, *lhs);
                    let phys_rhs = materialize(e, ra, &consts, *rhs);
                    maybe_free_with_cache(ra, local_cache, *lhs, inst_idx);
                    maybe_free_with_cache(ra, local_cache, *rhs, inst_idx);
                    let phys_dst = ra.alloc(*dst);
                    e.add_w(phys_dst, phys_lhs, phys_rhs);
                }
            }

            IrInst::Sub { dst, lhs, rhs } => {
                // Try immediate folding: sub wd, wn, #imm
                if let Some(imm) = consts.as_u12(*rhs) {
                    let phys_lhs = materialize(e, ra, &consts, *lhs);
                    maybe_free_with_cache(ra, local_cache, *lhs, inst_idx);
                    maybe_free_with_cache(ra, local_cache, *rhs, inst_idx);
                    let phys_dst = ra.alloc(*dst);
                    e.sub_w_imm(phys_dst, phys_lhs, imm);
                } else {
                    let phys_lhs = materialize(e, ra, &consts, *lhs);
                    let phys_rhs = materialize(e, ra, &consts, *rhs);
                    maybe_free_with_cache(ra, local_cache, *lhs, inst_idx);
                    maybe_free_with_cache(ra, local_cache, *rhs, inst_idx);
                    let phys_dst = ra.alloc(*dst);
                    e.sub_w(phys_dst, phys_lhs, phys_rhs);
                }
            }

            IrInst::Cmp {
                dst,
                lhs,
                rhs,
                cond,
            } => {
                let arm_cond = match cond {
                    IrCond::LeS => Cond::LE,
                };

                // Emit cmp (immediate or register).
                if let Some(imm) = consts.as_u12(*rhs) {
                    let phys_lhs = materialize(e, ra, &consts, *lhs);
                    maybe_free_with_cache(ra, local_cache, *lhs, inst_idx);
                    maybe_free_with_cache(ra, local_cache, *rhs, inst_idx);
                    e.cmp_w_imm(phys_lhs, imm);
                } else {
                    let phys_lhs = materialize(e, ra, &consts, *lhs);
                    let phys_rhs = materialize(e, ra, &consts, *rhs);
                    maybe_free_with_cache(ra, local_cache, *lhs, inst_idx);
                    maybe_free_with_cache(ra, local_cache, *rhs, inst_idx);
                    e.cmp_w_reg(phys_lhs, phys_rhs);
                }

                // Try fused compare-and-branch: peek at next instruction.
                let fused = try_fuse_cmp_branch(
                    insts,
                    inst_idx,
                    *dst,
                    arm_cond,
                    ra,
                    e,
                    label_offsets,
                    label_patches,
                );

                if fused {
                    // Skip the branch instruction (it was consumed).
                    inst_idx += 1;
                } else {
                    // No fusion — emit cset as usual.
                    let phys_dst = ra.alloc(*dst);
                    e.cset_w(phys_dst, arm_cond);
                }
            }

            IrInst::DefLabel { label } => {
                label_offsets[label.0 as usize] = Some(e.offset());
                // Conservative: clear cache at merge points.
                local_cache.clear();
            }

            IrInst::Br { label } => {
                if let Some(target) = label_offsets[label.0 as usize] {
                    let current = e.offset();
                    let word_offset = target as i32 - current as i32;
                    e.b_offset(word_offset);
                } else {
                    let pp = e.b();
                    label_patches.push((*label, pp));
                }
            }

            IrInst::BrIfZero { cond, label } => {
                let phys = materialize(e, ra, &consts, *cond);
                maybe_free_with_cache(ra, local_cache, *cond, inst_idx);
                emit_cbz_w(e, phys, *label, label_offsets, label_patches);
            }

            IrInst::BrIfNonZero { cond, label } => {
                let phys = materialize(e, ra, &consts, *cond);
                maybe_free_with_cache(ra, local_cache, *cond, inst_idx);
                emit_cbnz_w(e, phys, *label, label_offsets, label_patches);
            }

            IrInst::FrameStore { slot, src } => {
                let phys = materialize(e, ra, &consts, *src);
                maybe_free_with_cache(ra, local_cache, *src, inst_idx);
                e.str_x_uoff(phys, Reg::X29, (*slot as u16) * 8);
                // Update local cache if this slot corresponds to a local.
                if (*slot as usize) < ir.total_local_count as usize {
                    local_cache.set(*slot as usize, phys);
                }
            }

            IrInst::FrameLoad { dst, slot } => {
                let phys = ra.alloc(*dst);
                e.ldr_x_uoff(phys, Reg::X29, (*slot as u16) * 8);
            }

            IrInst::Call {
                func_idx,
                args,
                result,
            } => {
                // Move args into x9, x10, ... (scratch registers).
                // We need to be careful about conflicts — if an arg VReg
                // is already in the target register, skip the move.
                let arg_regs: Vec<Reg> = (0..args.len())
                    .map(|i| Reg(9 + i as u8))
                    .collect();
                for (i, &arg_vreg) in args.iter().enumerate() {
                    let src = materialize(e, ra, &consts, arg_vreg);
                    let dst = arg_regs[i];
                    if src != dst {
                        e.mov_x(dst, src);
                    }
                }
                // Free all scratch registers (they're clobbered by the call).
                ra.free_all();
                // All cached locals are invalid — registers are clobbered.
                local_cache.clear();

                // Advance frame base to callee's frame.
                let frame_sz = ir.frame_size() as u16;
                e.add_x_imm(Reg::X29, Reg::X29, frame_sz);

                // Emit the call.
                match call_mode {
                    CallMode::Indirect => {
                        let table_offset = (*func_idx as usize * 8) as u16;
                        e.ldr_x_uoff(Reg::X0, Reg::X20, CTX_FUNC_TABLE);
                        e.ldr_x_uoff(Reg::X0, Reg::X0, table_offset);
                        e.blr(Reg::X0);
                    }
                    CallMode::PcRelative { body_offsets, .. } => {
                        // Direct BL to body if target is already compiled.
                        if let Some(body_word) = body_offsets[*func_idx as usize] {
                            let current = e.offset();
                            let target = body_word as i32 - current as i32;
                            e.bl_offset(target);
                        } else {
                            // Fall back to jump table hop.
                            let current = e.offset();
                            let target = *func_idx as i32 - current as i32;
                            e.bl_offset(target);
                        }
                    }
                }

                // Restore frame base.
                e.sub_x_imm(Reg::X29, Reg::X29, frame_sz);

                // Move result from x9 to the result VReg's register.
                if let Some(r) = result {
                    let dst = ra.alloc(*r);
                    if dst != Reg::X9 {
                        e.mov_x(dst, Reg::X9);
                    }
                }
            }

            IrInst::Return { results } => {
                // Materialize any lazy-const results before emitting return.
                for &vreg in results.iter() {
                    materialize(e, ra, &consts, vreg);
                }
                emit_ir_return(e, ra, results, result_count);
            }

            IrInst::FuelCheck => {
                emit_fuel_check(e, fuel_sites);
            }

            IrInst::Trap => {
                e.code.push(0xD4200020); // BRK #1
            }
        }

        inst_idx += 1;
    }
}

/// Try to fuse a Cmp with a following BrIfZero/BrIfNonZero.
///
/// If the next instruction branches on `cmp_dst` and that's the only use
/// of the cset result, emit a conditional branch directly (saving the
/// cset + cbz/cbnz pair). Returns true if fusion happened.
fn try_fuse_cmp_branch(
    insts: &[IrInst],
    cmp_idx: usize,
    cmp_dst: VReg,
    arm_cond: Cond,
    ra: &mut RegAlloc,
    e: &mut Emitter,
    label_offsets: &[Option<usize>],
    label_patches: &mut Vec<(Label, PatchPoint)>,
) -> bool {
    let next_idx = cmp_idx + 1;
    if next_idx >= insts.len() {
        return false;
    }

    let (branch_cond_vreg, label, is_nonzero) = match &insts[next_idx] {
        IrInst::BrIfZero { cond, label } => (*cond, *label, false),
        IrInst::BrIfNonZero { cond, label } => (*cond, *label, true),
        _ => return false,
    };

    // Only fuse if the branch uses the Cmp's result.
    if branch_cond_vreg != cmp_dst {
        return false;
    }

    // Only fuse if this is the last use of the cmp result (next_idx).
    // This means nothing else reads the cset value, so we can skip it.
    if ra.last_use[cmp_dst.0 as usize] != next_idx {
        return false;
    }

    // Determine the branch condition:
    // BrIfNonZero on cset(cond) → branch if cond is true → use arm_cond
    // BrIfZero on cset(cond) → branch if cond is false → use inverted arm_cond
    let branch_arm_cond = if is_nonzero {
        arm_cond
    } else {
        arm_cond.invert()
    };

    // Free the cmp_dst VReg (it was never allocated, and won't be).
    // The BrIfZero/BrIfNonZero's maybe_free would have freed it at next_idx,
    // but since we're skipping that instruction, we handle it here.
    // Since we never allocated cmp_dst (no cset), there's nothing to free.

    // Emit b.cond.
    emit_b_cond(e, branch_arm_cond, label, label_offsets, label_patches);

    true
}

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
    // ---- Jump table: one `b <stub>` per function ----
    // We emit placeholders, then patch each to its interpret stub.
    let jump_table_pps: Vec<PatchPoint> = (0..func_count).map(|_| e.b()).collect();

    // ---- Interpret stubs: `mov w0, #idx; b interpret_exit` ----
    // We don't know interpret_exit yet, so collect patch points.
    let mut interpret_exit_pps: Vec<PatchPoint> = Vec::with_capacity(func_count);
    for (i, jt_pp) in jump_table_pps.iter().enumerate() {
        // Patch jump table entry → this stub.
        e.patch(*jt_pp);
        emit_i32_const_reg(e, Reg::W0, i as i32);
        interpret_exit_pps.push(e.b());
    }

    // ---- Shared yield handler ----
    let yield_handler = e.offset();

    // Check is_fiber flag in context (use x0 as temp, outside VReg pool).
    e.ldr_x_uoff(Reg::X0, Reg::X20, CTX_IS_FIBER);
    let fiber_branch = e.cbnz_x(Reg::X0);

    // Non-fiber path: simple unwind.
    emit_i32_const_reg(e, Reg::W0, -1);
    e.ldr_x_post(Reg::X30, Reg::SP, 16);
    e.ret();

    // Fiber yield path.
    e.patch(fiber_branch);
    emit_fiber_yield(e);

    // ---- Shared completion handler ----
    let completion = e.offset();
    emit_fiber_complete(e);

    // ---- Shared interpret-exit handler ----
    let interpret_exit = e.offset();
    // For now: trap. Actual interpreter bridge is a follow-up.
    e.code.push(0xD4200040); // BRK #2

    // Patch interpret stubs → interpret_exit.
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
/// The emitter must already contain the shared preamble (jump table +
/// stubs + handlers). This function appends the function body and
/// returns the body's byte offset within the emitter.
pub fn lower_into(
    e: &mut Emitter,
    ir: &IrFunction,
    func_idx: u32,
    shared: &SharedHandlerOffsets,
    body_offsets: &mut [Option<usize>],
) -> FunctionLayout {
    let body_start = e.offset();

    // Record this function's body offset so self-recursive calls
    // (and later functions calling us) can use direct BL.
    body_offsets[func_idx as usize] = Some(body_start);

    let vreg_count = count_vregs(&ir.insts);
    let last_use = compute_last_use(&ir.insts, vreg_count);
    let mut ra = RegAlloc::new(vreg_count, last_use);

    let max_label = count_labels(&ir.insts);
    let mut label_offsets: Vec<Option<usize>> = vec![None; max_label as usize];
    let mut label_patches: Vec<(Label, PatchPoint)> = Vec::new();

    // Fuel check sites for cold stubs.
    let mut fuel_sites: Vec<FuelCheckSite> = Vec::new();

    // ---- Prologue ----
    // TODO: pointer authentication (pacibz / autibz) — disabled for now.
    // e.code.push(0xD503235F); // pacibz
    // Save return address (x29 is the wasm frame pointer, managed by caller).
    e.str_x_pre(Reg::X30, Reg::SP, -16);

    // Copy params from registers (x9, x10, ...) to local slots.
    for i in 0..ir.param_count {
        let src = Reg(9 + i as u8);
        e.str_x_uoff(src, Reg::X29, (i as u16) * 8);
    }

    // Zero-initialize extra locals (beyond params).
    let extra_locals = ir.total_local_count - ir.param_count;
    for i in 0..extra_locals {
        let offset = ((ir.param_count + i) as u16) * 8;
        e.str_x_uoff(Reg::XZR, Reg::X29, offset);
    }

    // Seed local cache: params are in registers after prologue stores.
    let mut local_cache = LocalCache::new(ir.total_local_count as usize);
    for i in 0..ir.param_count {
        local_cache.set(i as usize, Reg(9 + i as u8));
    }

    // ---- Lower each IR instruction ----
    lower_body(
        e,
        ir,
        &mut ra,
        &mut fuel_sites,
        &mut label_offsets,
        &mut label_patches,
        &CallMode::PcRelative {
            shared,
            body_offsets,
        },
        &mut local_cache,
        false, // no markers in shared mode
    );

    // ---- Cold fuel-check stubs ----
    // Each fuel check in the hot path is `subs; b.le <here>`.
    // The stub does `bl shared_yield_handler` then jumps back to resume.
    for site in &fuel_sites {
        e.patch(site.b_le_patch);
        // BL to shared yield handler (sets x30 for fiber resume).
        let current = e.offset();
        let yield_offset = shared.yield_handler as i32 - current as i32;
        e.bl_offset(yield_offset);
        // Branch back to resume point.
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
///
/// The jump table starts at word offset 0. Entry `func_idx` is at
/// word offset `func_idx`.
pub fn patch_jump_table(e: &mut Emitter, func_idx: u32, target_word: usize) {
    let source = func_idx as usize;
    let word_offset = target_word as i32 - source as i32;
    let imm26 = (word_offset as u32) & 0x03FF_FFFF;
    e.code[source] = 0x14000000 | imm26;
}

/// Emit the return sequence for IR results.
///
/// Moves result to x9 (register-passing convention), restores x30,
/// and returns. The caller reads the result from x9.
fn emit_ir_return(e: &mut Emitter, ra: &RegAlloc, results: &[VReg], result_count: usize) {
    if result_count == 1 {
        let phys = ra.get(results[0]);
        if phys != Reg::X9 {
            e.mov_x(Reg::X9, phys);
        }
    }
    // result_count == 0: nothing to move.
    // result_count > 1: not yet supported (would need multi-reg return).

    // Epilogue: restore return address, verify pointer auth, return.
    e.ldr_x_post(Reg::X30, Reg::SP, 16);
    // e.code.push(0xD50323DF); // autibz
    e.ret();
}

/// Info for a fuel check that needs cold-path patching.
struct FuelCheckSite {
    /// Patch point for the `b.le` that jumps to the cold stub.
    b_le_patch: PatchPoint,
    /// Word offset of the instruction after `b.le` — where execution
    /// resumes after a fiber yield/refuel.
    resume_offset: usize,
}

/// Emit a fuel check: `subs x21, x21, #1; bc.le <cold_stub>`.
///
/// Uses BC.cond (FEAT_HBC) to hint that this branch is consistent —
/// almost always not-taken (fuel > 0). The cold stub (emitted later)
/// does `bl yield_handler; b .resume` so the hot path is only 2
/// instructions.
fn emit_fuel_check(e: &mut Emitter, fuel_sites: &mut Vec<FuelCheckSite>) {
    e.subs_x_imm(Reg::X21, Reg::X21, 1);
    let b_le_patch = e.b_cond(Cond::LE);
    let resume_offset = e.offset();
    fuel_sites.push(FuelCheckSite {
        b_le_patch,
        resume_offset,
    });
}

/// Emit the fiber yield handler.
///
/// Saves resume LR, scratch registers (x9-x15), fuel (x21), locals
/// base (x29), and JIT SP to context, then switches to host stack.
fn emit_fiber_yield(e: &mut Emitter) {
    // Save resume point (x30 holds return address from `bl yield_handler`).
    e.str_x_uoff(Reg::X30, Reg::X20, CTX_RESUME_LR);
    // Save scratch registers (x9-x15) BEFORE using x9 as temp.
    e.stp_x_soff(Reg::X9, Reg::X10, Reg::X20, CTX_SCRATCH as i16);
    e.stp_x_soff(Reg(11), Reg(12), Reg::X20, (CTX_SCRATCH + 16) as i16);
    e.stp_x_soff(Reg(13), Reg(14), Reg::X20, (CTX_SCRATCH + 32) as i16);
    e.str_x_uoff(Reg(15), Reg::X20, CTX_SCRATCH + 48);
    // Now safe to use x9 as temp.
    e.mov_x_from_sp(Reg::X9);
    e.str_x_uoff(Reg::X9, Reg::X20, CTX_JIT_SP);
    e.str_x_uoff(Reg::X21, Reg::X20, CTX_SAVED_FUEL);
    e.str_x_uoff(Reg::X29, Reg::X20, CTX_SAVED_FP);
    // Restore host state.
    e.ldr_x_uoff(Reg::X9, Reg::X20, CTX_HOST_SP);
    e.ldp_x_soff(Reg::X29, Reg::X30, Reg::X20, CTX_HOST_FP as i16);
    e.ldr_x_uoff(Reg::X20, Reg::X20, CTX_HOST_CTX); // MUST be last x20 read
    e.mov_sp_from(Reg::X9);
    e.movz_w(Reg::W0, 0); // 0 = Suspended
    e.ret();
}

/// Emit the fiber completion handler.
///
/// Saves the result (x9) to context, restores host state, and returns
/// with status=1 (Complete).
fn emit_fiber_complete(e: &mut Emitter) {
    // Save result value (x9) to context before restoring host state.
    e.str_x_uoff(Reg::X9, Reg::X20, CTX_WASM_SP_OFF); // repurposed as result_value
    // Restore host state.
    e.ldr_x_uoff(Reg::X9, Reg::X20, CTX_HOST_SP);
    e.ldp_x_soff(Reg::X29, Reg::X30, Reg::X20, CTX_HOST_FP as i16);
    e.ldr_x_uoff(Reg::X20, Reg::X20, CTX_HOST_CTX); // MUST be last x20 read
    e.mov_sp_from(Reg::X9);
    e.movz_w(Reg::W0, 1); // 1 = Complete
    e.ret();
}

/// Emit a 32-bit constant into a W register (used in lowering, not for VRegs).
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

/// Emit a 64-bit constant into an X register.
fn emit_i64_const(e: &mut Emitter, rd: Reg, val: i64) {
    if val >= 0 && val < 65536 {
        e.movz_x(rd, val as u16);
    } else {
        // For small values and negative values, use the W-register path.
        emit_i32_const_reg(e, rd, val as i32);
    }
}

/// Count the maximum VReg index + 1.
fn count_vregs(insts: &[IrInst]) -> u32 {
    let mut max_vreg = 0u32;
    for inst in insts {
        for_each_def(inst, |vreg| {
            max_vreg = max_vreg.max(vreg.0 + 1);
        });
        for_each_use(inst, |vreg| {
            max_vreg = max_vreg.max(vreg.0 + 1);
        });
    }
    max_vreg
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
fn for_each_def(inst: &IrInst, mut f: impl FnMut(VReg)) {
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
        IrInst::FuelCheck => {}
        IrInst::Trap => {}
    }
}

