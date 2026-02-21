//! Copy-and-patch JIT compiler for aarch64 (Apple Silicon).
//!
//! Compiles WASM functions to native machine code at module load time.
//! Only supports a subset of opcodes (integer arithmetic, control flow, locals).
//! Functions with unsupported opcodes fall back to the interpreter.

use crate::runtime::module::*;

/// Executable machine code buffer.
pub struct JitCode {
    ptr: *mut u8,
    len: usize,
}

unsafe impl Send for JitCode {}
unsafe impl Sync for JitCode {}

impl JitCode {
    fn new(code: &[u8]) -> Self {
        unsafe {
            let len = code.len().max(4096);
            let ptr = libc::mmap(
                std::ptr::null_mut(),
                len,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_PRIVATE | libc::MAP_ANONYMOUS | libc::MAP_JIT,
                -1,
                0,
            ) as *mut u8;
            assert!(!ptr.is_null(), "mmap failed");
            std::ptr::copy_nonoverlapping(code.as_ptr(), ptr, code.len());
            libc::mprotect(ptr as _, len, libc::PROT_READ | libc::PROT_EXEC);
            Self::invalidate_icache(ptr, code.len());
            JitCode { ptr, len }
        }
    }

    #[cfg(target_arch = "aarch64")]
    unsafe fn invalidate_icache(ptr: *mut u8, len: usize) {
        unsafe extern "C" {
            fn sys_icache_invalidate(start: *mut u8, len: usize);
        }
        unsafe {
            sys_icache_invalidate(ptr, len);
        }
    }

    #[cfg(not(target_arch = "aarch64"))]
    unsafe fn invalidate_icache(_ptr: *mut u8, _len: usize) {}

    /// Call the compiled function.
    /// - locals: pointer to the locals area
    /// - stack: pointer to the value stack base
    /// - sp: current stack pointer index
    /// Returns new sp value.
    pub fn code_len(&self) -> usize {
        self.len
    }

    pub unsafe fn call(&self, locals: *mut u64, stack: *mut u64, sp: usize) -> usize {
        unsafe {
            let f: unsafe extern "C" fn(*mut u64, *mut u64, usize) -> usize =
                std::mem::transmute(self.ptr);
            f(locals, stack, sp)
        }
    }
}

impl Drop for JitCode {
    fn drop(&mut self) {
        unsafe {
            libc::munmap(self.ptr as _, self.len);
        }
    }
}

// ============================================================================
// Aarch64 instruction encoding
// ============================================================================

// Register convention:
//   x0 = arg: locals pointer    -> saved to x19
//   x1 = arg: stack base        -> saved to x20
//   x2 = arg: initial sp index  -> saved to x21 (runtime sp)
//   x19 = locals pointer (callee-saved)
//   x20 = stack base pointer (callee-saved)
//   x21 = runtime sp index (callee-saved)
//   x8, x9, x10 = scratch
const LOCALS: u32 = 19;
const STACK: u32 = 20;
const SP: u32 = 21;
const S0: u32 = 8;
const S1: u32 = 9;
const S2: u32 = 10;

fn mov_reg(rd: u32, rn: u32) -> u32 {
    0xaa0003e0 | (rn << 16) | rd
}
fn movz_x(rd: u32, imm16: u32, shift: u32) -> u32 {
    0xd2800000 | ((shift / 16) << 21) | ((imm16 & 0xFFFF) << 5) | rd
}
fn movk_x(rd: u32, imm16: u32, shift: u32) -> u32 {
    0xf2800000 | ((shift / 16) << 21) | ((imm16 & 0xFFFF) << 5) | rd
}
fn movz_w(rd: u32, imm16: u32, shift: u32) -> u32 {
    0x52800000 | ((shift / 16) << 21) | ((imm16 & 0xFFFF) << 5) | rd
}
fn movn_w(rd: u32, imm16: u32, shift: u32) -> u32 {
    0x12800000 | ((shift / 16) << 21) | ((imm16 & 0xFFFF) << 5) | rd
}
fn movk_w(rd: u32, imm16: u32, shift: u32) -> u32 {
    0x72800000 | ((shift / 16) << 21) | ((imm16 & 0xFFFF) << 5) | rd
}

/// STR Xrt, [Xn, Xm, LSL #3]  (register offset, scaled by 8)
fn str_x_reg(rt: u32, rn: u32, rm: u32) -> u32 {
    0xf8207800 | (rm << 16) | (rn << 5) | rt
}

/// LDR Xrt, [Xn, Xm, LSL #3]  (register offset, scaled by 8)
fn ldr_x_reg(rt: u32, rn: u32, rm: u32) -> u32 {
    0xf8607800 | (rm << 16) | (rn << 5) | rt
}

/// STR Xrt, [Xn, #uimm] (unsigned byte offset, must be 8-byte aligned)
fn str_x_imm(rt: u32, rn: u32, byte_offset: u32) -> u32 {
    let imm12 = byte_offset / 8;
    debug_assert!(imm12 < 4096, "str offset too large: {byte_offset}");
    0xf9000000 | (imm12 << 10) | (rn << 5) | rt
}

/// LDR Xrt, [Xn, #uimm] (unsigned byte offset, must be 8-byte aligned)
fn ldr_x_imm(rt: u32, rn: u32, byte_offset: u32) -> u32 {
    let imm12 = byte_offset / 8;
    debug_assert!(imm12 < 4096, "ldr offset too large: {byte_offset}");
    0xf9400000 | (imm12 << 10) | (rn << 5) | rt
}

fn add_w(rd: u32, rn: u32, rm: u32) -> u32 {
    0x0b000000 | (rm << 16) | (rn << 5) | rd
}
fn sub_w(rd: u32, rn: u32, rm: u32) -> u32 {
    0x4b000000 | (rm << 16) | (rn << 5) | rd
}
fn add_x(rd: u32, rn: u32, rm: u32) -> u32 {
    0x8b000000 | (rm << 16) | (rn << 5) | rd
}
fn add_x_imm(rd: u32, rn: u32, imm12: u32) -> u32 {
    debug_assert!(imm12 < 4096);
    0x91000000 | (imm12 << 10) | (rn << 5) | rd
}
fn sub_x_imm(rd: u32, rn: u32, imm12: u32) -> u32 {
    debug_assert!(imm12 < 4096);
    0xd1000000 | (imm12 << 10) | (rn << 5) | rd
}
fn cmp_w(rn: u32, rm: u32) -> u32 {
    0x6b000000 | (rm << 16) | (rn << 5) | 0x1f
}

/// CSET Wd, cond = CSINC Wd, WZR, WZR, invcond
fn cset_w(rd: u32, cond: u32) -> u32 {
    let inv = cond ^ 1;
    // CSINC: 0x1a800400 | (Rm<<16) | (cond<<12) | (Rn<<5) | Rd
    // Rm=Rn=WZR(31): 0x1a9f07e0
    0x1a9f07e0 | (inv << 12) | rd
}

const CC_LE: u32 = 13;

fn cbz_w(rt: u32, offset: i32) -> u32 {
    0x34000000 | (((offset as u32) & 0x7FFFF) << 5) | rt
}
fn cbnz_w(rt: u32, offset: i32) -> u32 {
    0x35000000 | (((offset as u32) & 0x7FFFF) << 5) | rt
}
fn b_imm(offset: i32) -> u32 {
    0x14000000 | ((offset as u32) & 0x3FFFFFF)
}
fn bl_imm(offset: i32) -> u32 {
    0x94000000 | ((offset as u32) & 0x3FFFFFF)
}
const RET: u32 = 0xd65f03c0;

// ============================================================================
// Emitter with runtime SP register
// ============================================================================

struct Emitter {
    code: Vec<u32>,
}

#[derive(Clone, Copy)]
enum PatchKind {
    Cbz,
    Cbnz,
    B,
}

struct Patch {
    idx: usize,
    kind: PatchKind,
}

struct BlockInfo {
    start_offset: usize,
    patches: Vec<Patch>,
    is_loop: bool,
    arity: usize,
    /// Compile-time SP at block entry (relative to function entry SP).
    /// Used for stack unwinding on BR.
    sp_at_entry: i32,
    /// Number of initial patches from IF/IF_ELSE (the CBZ).
    /// At ELSE, only these are patched to point to else_start;
    /// BR patches added during THEN body are kept for END.
    initial_patch_count: usize,
}

impl Emitter {
    fn new() -> Self {
        Emitter { code: Vec::new() }
    }
    fn emit(&mut self, instr: u32) {
        self.code.push(instr);
    }
    fn pos(&self) -> usize {
        self.code.len()
    }

    /// Prologue: save callee-saved regs, move args to callee-saved regs
    fn emit_prologue(&mut self) {
        self.emit(0xa9bf7bfd); // stp x29, x30, [sp, #-16]!
        self.emit(0xa9bf53f3); // stp x19, x20, [sp, #-16]!
        self.emit(0xa9bf5bf5); // stp x21, x22, [sp, #-16]!
        self.emit(mov_reg(LOCALS, 0)); // x19 = locals ptr
        self.emit(mov_reg(STACK, 1)); // x20 = stack base
        self.emit(mov_reg(SP, 2)); // x21 = sp index
    }

    /// Epilogue: return x21 (sp) in x0, restore callee-saved, ret
    fn emit_epilogue(&mut self) {
        self.emit(mov_reg(0, SP)); // x0 = x21 (current sp)
        self.emit(0xa8c15bf5); // ldp x21, x22, [sp], #16
        self.emit(0xa8c153f3); // ldp x19, x20, [sp], #16
        self.emit(0xa8c17bfd); // ldp x29, x30, [sp], #16
        self.emit(RET);
    }

    /// Push x_src to stack[sp], sp++
    fn emit_push(&mut self, src: u32) {
        // str src, [STACK, SP, lsl #3]
        self.emit(str_x_reg(src, STACK, SP));
        // add SP, SP, #1
        self.emit(add_x_imm(SP, SP, 1));
    }

    /// sp--, pop stack[sp] to x_dst
    fn emit_pop(&mut self, dst: u32) {
        // sub SP, SP, #1
        self.emit(sub_x_imm(SP, SP, 1));
        // ldr dst, [STACK, SP, lsl #3]
        self.emit(ldr_x_reg(dst, STACK, SP));
    }

    /// Peek stack[sp - 1] into dst (no sp change)
    fn emit_peek_top(&mut self, dst: u32) {
        // sub scratch, SP, #1
        self.emit(sub_x_imm(S2, SP, 1));
        // ldr dst, [STACK, S2, lsl #3]
        self.emit(ldr_x_reg(dst, STACK, S2));
    }

    fn emit_load_i32(&mut self, rd: u32, val: i32) {
        let v = val as u32;
        if val >= 0 && val < 0x10000 {
            self.emit(movz_w(rd, v, 0));
        } else if val < 0 && val >= -0x10000 {
            self.emit(movn_w(rd, (!v) & 0xFFFF, 0));
        } else {
            self.emit(movz_w(rd, v & 0xFFFF, 0));
            self.emit(movk_w(rd, (v >> 16) & 0xFFFF, 16));
        }
    }

    fn emit_load_u64(&mut self, rd: u32, val: u64) {
        let w0 = (val & 0xFFFF) as u32;
        let w1 = ((val >> 16) & 0xFFFF) as u32;
        let w2 = ((val >> 32) & 0xFFFF) as u32;
        let w3 = ((val >> 48) & 0xFFFF) as u32;
        self.emit(movz_x(rd, w0, 0));
        if w1 != 0 {
            self.emit(movk_x(rd, w1, 16));
        }
        if w2 != 0 {
            self.emit(movk_x(rd, w2, 32));
        }
        if w3 != 0 {
            self.emit(movk_x(rd, w3, 48));
        }
    }

    fn emit_patch(&mut self, kind: PatchKind) -> Patch {
        let idx = self.pos();
        self.emit(0); // placeholder
        Patch { idx, kind }
    }

    fn apply_patch(&mut self, patch: &Patch) {
        let offset = self.pos() as i32 - patch.idx as i32;
        self.code[patch.idx] = match patch.kind {
            PatchKind::Cbz => cbz_w(S0, offset),
            PatchKind::Cbnz => cbnz_w(S0, offset),
            PatchKind::B => b_imm(offset),
        };
    }

    fn finalize(self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(self.code.len() * 4);
        for w in &self.code {
            bytes.extend_from_slice(&w.to_le_bytes());
        }
        bytes
    }
}

// ============================================================================
// Compiler
// ============================================================================

fn is_supported(code: u8) -> bool {
    matches!(
        code,
        OP_NOP
            | OP_LOCAL_GET
            | OP_LOCAL_SET
            | OP_LOCAL_TEE
            | OP_I32_CONST
            | OP_I32_ADD
            | OP_I32_SUB
            | OP_I32_LE_S
            | OP_IF
            | OP_IF_ELSE
            | OP_ELSE
            | OP_END
            | OP_BLOCK
            | OP_LOOP
            | OP_BR
            | OP_BR_IF
            | OP_RETURN
            | OP_CALL
            | OP_LOCAL_GET_I32_CONST
            | OP_LOCAL_GET_LOCAL_GET
            | OP_DROP
    )
}

/// Try to compile a function to native aarch64 code.
pub fn compile_func(func: &FuncDef, module: &Module, func_idx: u32) -> Option<JitCode> {
    for op in &func.body {
        if !is_supported(op.code) {
            return None;
        }
        // Only support self-recursive calls for now (BL to function start).
        // Cross-function calls would need separate compilation or a trampoline.
        if op.code == OP_CALL && op.imm_u32() != func_idx {
            return None;
        }
    }

    let mut e = Emitter::new();
    e.emit_prologue();

    let func_arity = module.types[func.type_idx as usize].results().len();
    let mut blocks: Vec<BlockInfo> = Vec::new();

    // Compile-time SP tracking (relative to initial SP at function entry).
    // Initial SP = number of locals (set by caller).
    let mut ct_sp: i32 = 0;

    // Implicit function block
    blocks.push(BlockInfo {
        start_offset: e.pos(),
        patches: Vec::new(),
        is_loop: false,
        arity: func_arity,
        sp_at_entry: ct_sp,
        initial_patch_count: 0,
    });

    for op in func.body.iter() {
        match op.code {
            OP_NOP => {}

            OP_LOCAL_GET => {
                let idx = op.imm_u32();
                e.emit(ldr_x_imm(S0, LOCALS, idx * 8));
                e.emit_push(S0);
                ct_sp += 1;
            }

            OP_LOCAL_SET => {
                let idx = op.imm_u32();
                e.emit_pop(S0);
                e.emit(str_x_imm(S0, LOCALS, idx * 8));
                ct_sp -= 1;
            }

            OP_LOCAL_TEE => {
                let idx = op.imm_u32();
                e.emit_peek_top(S0);
                e.emit(str_x_imm(S0, LOCALS, idx * 8));
            }

            OP_I32_CONST => {
                e.emit_load_i32(S0, op.imm_i32());
                e.emit_push(S0);
                ct_sp += 1;
            }

            OP_I32_ADD => {
                e.emit_pop(S1);
                e.emit_pop(S0);
                e.emit(add_w(S0, S0, S1));
                e.emit_push(S0);
                ct_sp -= 1; // net: -2 + 1 = -1
            }

            OP_I32_SUB => {
                e.emit_pop(S1);
                e.emit_pop(S0);
                e.emit(sub_w(S0, S0, S1));
                e.emit_push(S0);
                ct_sp -= 1;
            }

            OP_I32_LE_S => {
                e.emit_pop(S1);
                e.emit_pop(S0);
                e.emit(cmp_w(S0, S1));
                e.emit(cset_w(S0, CC_LE));
                e.emit_push(S0);
                ct_sp -= 1;
            }

            OP_DROP => {
                e.emit(sub_x_imm(SP, SP, 1));
                ct_sp -= 1;
            }

            OP_BLOCK => {
                let arity = op.imm_lo() as usize;
                blocks.push(BlockInfo {
                    start_offset: e.pos(),
                    patches: Vec::new(),
                    is_loop: false,
                    arity,
                    sp_at_entry: ct_sp,
                    initial_patch_count: 0,
                });
            }

            OP_LOOP => {
                let arity = op.imm_u32() as usize;
                blocks.push(BlockInfo {
                    start_offset: e.pos(),
                    patches: Vec::new(),
                    is_loop: true,
                    arity,
                    sp_at_entry: ct_sp,
                    initial_patch_count: 0,
                });
            }

            OP_IF => {
                let arity = op.imm_lo() as usize;
                e.emit_pop(S0);
                ct_sp -= 1;
                let patch = e.emit_patch(PatchKind::Cbz);
                blocks.push(BlockInfo {
                    start_offset: e.pos(),
                    patches: vec![patch],
                    is_loop: false,
                    arity,
                    sp_at_entry: ct_sp,
                    initial_patch_count: 1,
                });
            }

            OP_IF_ELSE => {
                let arity = (op.imm >> 56) as usize;
                e.emit_pop(S0);
                ct_sp -= 1;
                let patch = e.emit_patch(PatchKind::Cbz);
                blocks.push(BlockInfo {
                    start_offset: e.pos(),
                    patches: vec![patch],
                    is_loop: false,
                    arity,
                    sp_at_entry: ct_sp,
                    initial_patch_count: 1,
                });
            }

            OP_ELSE => {
                let block = blocks.last_mut().unwrap();
                // At the end of the "then" branch, SP should be sp_at_entry + arity.
                // Reset ct_sp to sp_at_entry for the "else" branch.
                let end_patch = e.emit_patch(PatchKind::B);
                // Only apply initial patches (CBZ from IF/IF_ELSE) to point to else_start.
                // Keep BR patches from THEN body — they should point to END.
                let initial_count = block.initial_patch_count;
                let remaining: Vec<Patch> = block.patches.drain(initial_count..).collect();
                for p in block.patches.drain(..) {
                    e.apply_patch(&p);
                }
                block.patches = remaining;
                block.patches.push(end_patch);
                block.initial_patch_count = 0;
                ct_sp = block.sp_at_entry;
            }

            OP_END => {
                if let Some(block) = blocks.pop() {
                    for p in &block.patches {
                        e.apply_patch(p);
                    }
                    // After block END, SP should be sp_at_entry + arity
                    ct_sp = block.sp_at_entry + block.arity as i32;

                    // If this was the function-level block (blocks is now empty),
                    // store results at locals[0..arity] and return.
                    if blocks.is_empty() && func_arity > 0 {
                        // Results are on the operand stack at stack[SP-arity..SP]
                        for i in (0..func_arity).rev() {
                            e.emit_pop(S0);
                            e.emit(str_x_imm(S0, LOCALS, i as u32 * 8));
                        }
                    }
                }
            }

            OP_BR => {
                let depth = op.imm_u32() as usize;
                let target_idx = blocks.len() - 1 - depth;
                let target = &blocks[target_idx];
                if target.is_loop {
                    // For loops, BR goes back to loop start. Stack unwind to loop's entry height.
                    let excess = ct_sp - target.sp_at_entry;
                    if excess > 0 {
                        e.emit(sub_x_imm(SP, SP, excess as u32));
                    }
                    let offset = target.start_offset as i32 - e.pos() as i32;
                    e.emit(b_imm(offset));
                } else {
                    // For blocks, BR jumps to block END. Stack should be sp_at_entry + arity.
                    // We need to keep top `arity` values and discard the rest.
                    let target_arity = target.arity;
                    let target_sp = target.sp_at_entry;
                    let excess = ct_sp - target_sp - target_arity as i32;
                    if excess > 0 && target_arity > 0 {
                        if target_arity == 1 {
                            // Pop result, discard excess values, push result back.
                            // After pop: SP = initial + ct_sp - 1
                            // Want: SP = initial + target_sp (push will make target_sp + 1)
                            // Adjust = (ct_sp - 1) - target_sp = excess
                            e.emit_pop(S0);
                            e.emit(sub_x_imm(SP, SP, excess as u32));
                            e.emit_push(S0);
                        } else {
                            return None;
                        }
                    } else if excess > 0 && target_arity == 0 {
                        // Just discard excess values
                        e.emit(sub_x_imm(SP, SP, excess as u32));
                    }
                    let patch = e.emit_patch(PatchKind::B);
                    blocks[target_idx].patches.push(patch);
                }
                // After unconditional BR, ct_sp is unreachable but will be
                // reset by the next END/ELSE. Set to target for safety.
                // Actually, code after unconditional BR is dead code.
                // ct_sp doesn't matter here, it'll be reset.
            }

            OP_BR_IF => {
                let depth = op.imm_u32() as usize;
                let target_idx = blocks.len() - 1 - depth;
                let target = &blocks[target_idx];
                e.emit_pop(S0); // pop condition
                ct_sp -= 1;
                if target.is_loop {
                    // For loops, stack unwind to loop's entry height
                    let excess = ct_sp - target.sp_at_entry;
                    if excess > 0 {
                        // Can't easily do conditional stack adjustment without a branch
                        // Emit: if cond != 0, adjust SP and branch
                        // cbz S0, skip; sub SP, excess; b loop_start; skip:
                        let skip_patch = e.emit_patch(PatchKind::Cbz);
                        e.emit(sub_x_imm(SP, SP, excess as u32));
                        let offset = target.start_offset as i32 - e.pos() as i32;
                        e.emit(b_imm(offset));
                        e.apply_patch(&skip_patch);
                    } else {
                        let offset = target.start_offset as i32 - e.pos() as i32;
                        e.emit(cbnz_w(S0, offset));
                    }
                } else {
                    let target_arity = target.arity;
                    let target_sp = target.sp_at_entry;
                    let excess = ct_sp - target_sp - target_arity as i32;
                    if excess > 0 {
                        // Need conditional stack unwinding
                        // cbz S0, skip; <unwind>; b end; skip:
                        let skip_patch = e.emit_patch(PatchKind::Cbz);
                        if target_arity == 1 {
                            // Pop result, adjust, push back
                            e.emit_pop(S1); // temporarily use S1 since S0 has condition
                            e.emit(sub_x_imm(SP, SP, excess as u32));
                            e.emit_push(S1);
                        } else if target_arity == 0 {
                            e.emit(sub_x_imm(SP, SP, excess as u32));
                        } else {
                            return None;
                        }
                        let br_patch = e.emit_patch(PatchKind::B);
                        blocks[target_idx].patches.push(br_patch);
                        e.apply_patch(&skip_patch);
                    } else {
                        let patch = e.emit_patch(PatchKind::Cbnz);
                        blocks[target_idx].patches.push(patch);
                    }
                }
            }

            OP_RETURN => {
                let arity = func_arity;
                if arity == 1 {
                    e.emit_pop(S0);
                    e.emit(str_x_imm(S0, LOCALS, 0));
                } else if arity > 1 {
                    for i in (0..arity).rev() {
                        e.emit_pop(S0);
                        e.emit(str_x_imm(S0, LOCALS, i as u32 * 8));
                    }
                }
                e.emit_epilogue();
                // Dead code after return; ct_sp doesn't matter
            }

            OP_CALL => {
                let callee_idx = op.imm_u32();
                let callee = match module.get_func(callee_idx) {
                    Some(f) => f,
                    None => return None,
                };
                let callee_type = &module.types[callee.type_idx as usize];
                let param_count = callee_type.params().len();
                let local_count = callee.locals.len();
                let extra_locals = local_count - param_count;
                let result_count = callee_type.results().len();

                // Zero extra locals by pushing 0s
                if extra_locals > 0 {
                    e.emit(movz_x(S0, 0, 0));
                    for _ in 0..extra_locals {
                        e.emit_push(S0);
                    }
                    ct_sp += extra_locals as i32;
                }

                // x0 = locals ptr = &stack[SP - local_count]
                e.emit(sub_x_imm(S2, SP, local_count as u32));
                emit_add_lsl3(&mut e, 0, STACK, S2);

                // x1 = STACK (stack base)
                e.emit(mov_reg(1, STACK));

                // x2 = SP (current sp = after locals)
                e.emit(mov_reg(2, SP));

                // BL to self (recursive call to this same function)
                let bl_offset = -(e.pos() as i32);
                e.emit(bl_imm(bl_offset));

                // After return: callee-saved regs restored, our SP is intact.
                // The callee stored results at locals[0..result_count].
                // Pop off the locals area and push results:
                e.emit(sub_x_imm(SP, SP, local_count as u32));
                if result_count > 0 {
                    e.emit(add_x_imm(SP, SP, result_count as u32));
                }
                // ct_sp tracking:
                // Before CALL: ct_sp already has +extra_locals from pushes above.
                // Runtime: sub local_count, add result_count.
                // So: ct_sp += -local_count + result_count
                // = -(param_count + extra_locals) + result_count
                // Combined with the +extra_locals above:
                // net = -param_count + result_count
                ct_sp -= local_count as i32;
                ct_sp += result_count as i32;
            }

            OP_LOCAL_GET_I32_CONST => {
                let idx = op.imm_hi();
                let val = op.imm_lo() as i32;
                e.emit(ldr_x_imm(S0, LOCALS, idx * 8));
                e.emit_push(S0);
                e.emit_load_i32(S0, val);
                e.emit_push(S0);
                ct_sp += 2;
            }

            OP_LOCAL_GET_LOCAL_GET => {
                let a = op.imm_hi();
                let b = op.imm_lo();
                e.emit(ldr_x_imm(S0, LOCALS, a * 8));
                e.emit_push(S0);
                e.emit(ldr_x_imm(S0, LOCALS, b * 8));
                e.emit_push(S0);
                ct_sp += 2;
            }

            _ => return None,
        }
    }

    e.emit_epilogue();
    let code = e.finalize();
    Some(JitCode::new(&code))
}

// Helper: ADD Xd, Xn, Xm, LSL #3
fn add_lsl3(rd: u32, rn: u32, rm: u32) -> u32 {
    // ADD Xd, Xn, Xm, LSL #3
    // Encoding: 0x8b000000 | (shift << 10) | ...
    // Actually: ADD (extended register) or ADD (shifted register)
    // ADD Xd, Xn, Xm, LSL #3 = 0x8b000000 | (rm << 16) | (0b01 << 22) | (3 << 10) | (rn << 5) | rd
    // Wait, the shift field for shifted register is:
    // 0x8b000000 | (rm << 16) | (rn << 5) | rd  with shift = (imm6 << 10), type = (shift_type << 22)
    // LSL = 00, so shift_type = 0b00
    0x8b000000 | (rm << 16) | (3 << 10) | (rn << 5) | rd
}

// Need this as a separate function since we can't call methods on self while borrowing e mutably
fn emit_add_lsl3(e: &mut Emitter, rd: u32, rn: u32, rm: u32) {
    e.emit(add_lsl3(rd, rn, rm));
}
