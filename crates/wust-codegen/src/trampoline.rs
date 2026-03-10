//! AArch64 entry trampoline generation.
//!
//! Generates raw machine code for the entry trampoline that bridges
//! the inline-asm calling convention to the JIT function body.
//! This is aarch64-specific and will likely be replaced by a
//! backend-generic mechanism later.

use wust_core::{FRAME_HEADER_SIZE, FuncMeta, Outcome, slot_size};

/// Generate the entry trampoline as raw machine code bytes.
///
/// The trampoline bridges the inline-asm calling convention to the
/// JIT function body:
///
/// 1. Save lr on fibre stack (sp)
/// 2. Convert x29 from wasm_fp.ptr to locals base (g.lb)
/// 3. Load parameters from local slots into x9+
/// 4. bl to function body
/// 5. Restore x29 to wasm_fp.ptr
/// 6. Store results from x9+ to operand base
/// 7. Restore lr from fibre stack
/// 8. ret
pub fn emit_entry_trampoline(func: &FuncMeta) -> Vec<u8> {
    let locals_header_size = func.locals_size as u32 + FRAME_HEADER_SIZE as u32;
    let mut words: Vec<u32> = Vec::with_capacity(16);

    // str x30, [sp, #-16]!   — save lr on fibre stack (16-byte aligned)
    words.push(encode_str_pre(30, 31, -16));

    // sub x29, x29, #locals_header_size  — convert to locals base
    words.push(encode_sub_imm_x(29, 29, locals_header_size));

    // Load parameters from local slots into calling convention regs (x0, x1, ...)
    for (i, &off) in func.local_byte_offsets[..func.param_count()]
        .iter()
        .enumerate()
        .take(7)
    {
        // ldr w(i), [x29, #off]  — 32-bit unsigned offset load
        words.push(encode_ldr_w_uoff(i as u32, 29, off as u32));
    }

    // bl to function body — offset in words from this instruction
    // Body starts right after the trampoline.
    let bl_word_idx = words.len();
    // Total trampoline size = bl_word_idx + 1 (bl) + 1 (add) + results (str) + 1 (ldr_post) + 1 (ret)
    let total_trampoline = bl_word_idx + 1 + 1 + func.result_count().min(7) + 1 + 1;
    let bl_offset = total_trampoline as i32 - bl_word_idx as i32;
    words.push(encode_bl(bl_offset));

    // add x29, x29, #locals_header_size  — restore to wasm_fp.ptr
    words.push(encode_add_imm_x(29, 29, locals_header_size));

    // Store results from calling convention regs to operand base (wasm_fp.ptr = x29)
    let mut result_offset = 0u32;
    for (i, ty) in func.results.iter().enumerate().take(7) {
        // str w(i), [x29, #result_offset]
        words.push(encode_str_w_uoff(i as u32, 29, result_offset));
        result_offset += slot_size(*ty) as u32 * 4;
    }

    // ldr x30, [sp], #16  — restore lr from fibre stack
    words.push(encode_ldr_post(30, 31, 16));

    // ret x30
    words.push(encode_ret(30));

    debug_assert_eq!(
        words.len(),
        total_trampoline,
        "trampoline size mismatch: predicted {total_trampoline}, got {}",
        words.len()
    );

    let mut bytes = Vec::with_capacity(words.len() * 4);
    for word in words {
        bytes.extend_from_slice(&word.to_le_bytes());
    }
    bytes
}

/// Call the JIT entry trampoline with the appropriate register setup.
///
/// Register convention on entry to trampoline:
/// - x27 = fuel counter (g.fuel)
/// - x29 = wasm_fp.ptr (operand base, past header)
/// - sp  = fibre stack pointer
///
/// The trampoline converts x29 to locals base, loads params,
/// calls the function body, stores results, and returns.
pub fn call_trampoline(trampoline_ptr: *const u8, ctx: &mut wust_core::Context) -> Outcome {
    const FUEL: usize = std::mem::offset_of!(wust_core::Context, fuel);
    const WASM_FP: usize = std::mem::offset_of!(wust_core::Context, wasm_fp);
    const FIBRE_SP: usize = std::mem::offset_of!(wust_core::Context, fibre_sp);

    let ctx_ptr = ctx as *mut wust_core::Context as u64;

    unsafe {
        std::arch::asm!(
            // Save host callee-saved registers on host stack.
            "stp x29, x30, [sp, #-16]!",
            "stp x28, x27, [sp, #-16]!",
            "stp x26, x25, [sp, #-16]!",
            "stp x24, x23, [sp, #-16]!",
            "stp x22, x21, [sp, #-16]!",
            "stp x20, x19, [sp, #-16]!",

            // Save ctx pointer on host stack.
            "str {ctx}, [sp, #-16]!",

            // Load JIT state from context.
            // fuel=x28, ctx=x27, fp=x29 (matches JIT register assignments).
            "ldr x28, [{ctx}, #{fuel}]",
            "ldr x29, [{ctx}, #{fp}]",

            // Switch to fibre stack: save host SP on fibre stack, then swap.
            // Use x1 as temp for both host sp and fibre sp.
            "mov x1, sp",                           // x1 = host sp
            "ldr x2, [{ctx}, #{fibre_sp}]",         // x2 = fibre sp
            "str x1, [x2, #-16]!",                 // push host sp onto fibre stack
            "mov sp, x2",                           // switch to fibre stack

            // Call the entry trampoline (sp = fibre stack).
            "blr {code}",

            // After JIT returns: sp = fibre stack (trampoline popped its LR).
            // Pop host sp from fibre stack.
            "ldr x1, [sp], #16",                    // x1 = host sp
            "mov x2, sp",                           // x2 = current fibre sp
            "mov sp, x1",                           // restore host sp

            // Reload ctx from host stack, store JIT state back.
            "ldr x3, [sp], #16",
            "str x28, [x3, #{fuel}]",
            "str x29, [x3, #{fp}]",
            "str x2, [x3, #{fibre_sp}]",

            // Restore host callee-saved registers.
            "ldp x20, x19, [sp], #16",
            "ldp x22, x21, [sp], #16",
            "ldp x24, x23, [sp], #16",
            "ldp x26, x25, [sp], #16",
            "ldp x28, x27, [sp], #16",
            "ldp x29, x30, [sp], #16",

            ctx = in(reg) ctx_ptr,
            code = in(reg) trampoline_ptr,
            fuel = const FUEL,
            fp = const WASM_FP,
            fibre_sp = const FIBRE_SP,
            // Clobbers: all caller-saved registers the JIT might use.
            out("x0") _, out("x1") _, out("x2") _, out("x3") _,
            out("x4") _, out("x5") _,
            out("x6") _, out("x7") _, out("x8") _,
            out("x9") _, out("x10") _, out("x11") _,
            out("x12") _, out("x13") _, out("x14") _,
            out("x15") _, out("x16") _, out("x17") _,
        );
    }

    Outcome::Return
}

// --- Raw aarch64 instruction encoders ---

/// `str Xt, [Xn, #simm9]!` (pre-index, 64-bit)
fn encode_str_pre(rt: u32, rn: u32, imm9: i32) -> u32 {
    let imm9_bits = ((imm9 as u32) & 0x1FF) << 12;
    0xF8000C00 | imm9_bits | (rn << 5) | rt
}

/// `ldr Xt, [Xn], #simm9` (post-index, 64-bit)
fn encode_ldr_post(rt: u32, rn: u32, imm9: i32) -> u32 {
    let imm9_bits = ((imm9 as u32) & 0x1FF) << 12;
    0xF8400400 | imm9_bits | (rn << 5) | rt
}

/// `sub Xd, Xn, #imm12` (64-bit)
fn encode_sub_imm_x(rd: u32, rn: u32, imm12: u32) -> u32 {
    debug_assert!(imm12 < 4096, "imm12 out of range: {imm12}");
    0xD1000000 | (imm12 << 10) | (rn << 5) | rd
}

/// `add Xd, Xn, #imm12` (64-bit)
fn encode_add_imm_x(rd: u32, rn: u32, imm12: u32) -> u32 {
    debug_assert!(imm12 < 4096, "imm12 out of range: {imm12}");
    0x91000000 | (imm12 << 10) | (rn << 5) | rd
}

/// `ldr Wt, [Xn, #uimm12*4]` (32-bit unsigned offset)
fn encode_ldr_w_uoff(rt: u32, rn: u32, byte_offset: u32) -> u32 {
    debug_assert!(
        byte_offset % 4 == 0,
        "offset must be 4-byte aligned: {byte_offset}"
    );
    let scaled = byte_offset / 4;
    debug_assert!(scaled < 4096, "scaled offset out of range: {scaled}");
    0xB9400000 | (scaled << 10) | (rn << 5) | rt
}

/// `str Wt, [Xn, #uimm12*4]` (32-bit unsigned offset)
fn encode_str_w_uoff(rt: u32, rn: u32, byte_offset: u32) -> u32 {
    debug_assert!(
        byte_offset % 4 == 0,
        "offset must be 4-byte aligned: {byte_offset}"
    );
    let scaled = byte_offset / 4;
    debug_assert!(scaled < 4096, "scaled offset out of range: {scaled}");
    0xB9000000 | (scaled << 10) | (rn << 5) | rt
}

/// `bl #offset` (offset in words, signed 26-bit)
fn encode_bl(word_offset: i32) -> u32 {
    let imm26 = (word_offset as u32) & 0x03FFFFFF;
    0x94000000 | imm26
}

/// `ret Xn`
fn encode_ret(rn: u32) -> u32 {
    0xD65F0000 | (rn << 5)
}
