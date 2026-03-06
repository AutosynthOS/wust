use crate::code_buffer::CodeBuffer;

/// Hardcoded fib function using raw aarch64 machine code.
///
/// This is the target output — the code that wust's compiler should
/// eventually generate via the autosynth-codegen API. For now we emit
/// it manually to prove the code buffer works end-to-end.
///
/// Register convention (matches wust JIT):
///   x29 (g.lb)   = locals base pointer
///   x21 (g.fuel) = fuel counter
///   x30 (g.lr)   = link register (saved/restored via fiber stack)
///   sp  (g.sp)   = fiber stack pointer
///   x9           = first param / return value (i32, uses w9)
///
/// Frame layout from x29:
///   [+0x00] local 0: param n  (i32, 4 bytes)
///   [+0x04] local 1: a        (i32, 4 bytes)
///   [+0x08] local 2: b        (i32, 4 bytes)
///   [+0x0C] frame header: func_idx   (u32)
///   [+0x10] frame header: resume_pc  (u32)
///   [+0x14] frame header: prev_fp_offset (u32)
///   Total frame advance = 0x18 (24 bytes)
#[test]
fn fib_10_returns_55() {
    let mut buf = CodeBuffer::new(4096).unwrap();

    // We'll emit the fib function body, then an entry stub that sets
    // up the calling convention and calls it.

    // --- fib function body ---
    let fib_offset = buf.len();

    // 0000: str x30, [sp, #-16]!          ; prologue — save LR on fiber stack
    buf.emit_u32(0xF81F0FE0 | 30);         // STR X30, [SP, #-16]!

    // 0004: movz x10, #0                  ; local.a = local.b = 0 (not strictly needed, frame is zeroed)
    buf.emit_u32(0xD280000A);              // MOVZ X10, #0

    // 0008: subs wzr, w9, #1              ; compare n <= 1
    buf.emit_u32(0x7100053F);              // SUBS WZR, W9, #1

    // 000C: b.gt +4 instructions → 001C   ; if n > 1, skip early return
    buf.emit_u32(0x54000060 | 0x0C);       // B.GT #3 (3 words forward) | GT=0xC

    // 0010: sub x21, x21, #3              ; fuel consume (early return path)
    buf.emit_u32(0xD1000EB5);              // SUB X21, X21, #3

    // 0014: add sp, sp, #16               ; restore fiber stack
    buf.emit_u32(0x910043FF);              // ADD SP, SP, #16

    // 0018: ret                           ; return w9 (param n, already in place)
    buf.emit_u32(0xD65F03C0);

    // 001C: sub w12, w9, #1               ; n - 1
    buf.emit_u32(0x5100052C);              // SUB W12, W9, #1

    // 0020: str w9, [x29]                 ; spill local.n
    buf.emit_u32(0xB90003A9);              // STR W9, [X29, #0]

    // 0024: subs x21, x21, #2             ; fuel consume
    buf.emit_u32(0xF10008B5);              // SUBS X21, X21, #2

    // 0028: b.le → suspend_0 (at 0074)    ; fuel check
    //        offset = (0x74 - 0x28) / 4 = 19 words
    buf.emit_u32(0x5400026D);              // B.LE #19 | LE=0xD

    // 002C: orr w9, wzr, w12              ; mov w9, w12 (arg = n-1)
    buf.emit_u32(0x2A0C03E9);              // ORR W9, WZR, W12

    // 0030: add x29, x29, #24             ; frame advance
    buf.emit_u32(0x910063BD);              // ADD X29, X29, #0x18

    // 0034: bl fib (self-recursive, offset = fib_offset - current)
    //        offset = (0x00 - 0x34) / 4 = -13 words
    buf.emit_u32(0x97FFFFF3);              // BL #-13

    // 0038: sub x29, x29, #24             ; frame restore
    buf.emit_u32(0xD10063BD);              // SUB X29, X29, #0x18

    // 003C: ldr w10, [x29]                ; reload local.n
    buf.emit_u32(0xB94003AA);              // LDR W10, [X29, #0]

    // 0040: orr w11, wzr, w9              ; mov w11, w9 (save fib(n-1) result)
    buf.emit_u32(0x2A0903EB);              // ORR W11, WZR, W9

    // 0044: sub w9, w10, #2               ; n - 2
    buf.emit_u32(0x51000949);              // SUB W9, W10, #2

    // 0048: str w11, [x29, #4]            ; store local.a = fib(n-1)
    buf.emit_u32(0xB90007AB);              // STR W11, [X29, #4]

    // 004C: subs x21, x21, #2             ; fuel consume
    buf.emit_u32(0xF10008B5);              // SUBS X21, X21, #2

    // 0050: b.le → suspend_1 (at 0x8C)
    //        offset = (0x8C - 0x50) / 4 = 15 words
    buf.emit_u32(0x540001ED);              // B.LE #15 | LE=0xD

    // 0054: add x29, x29, #24             ; frame advance
    buf.emit_u32(0x910063BD);              // ADD X29, X29, #0x18

    // 0058: bl fib (offset = (0x00 - 0x58) / 4 = -22 words)
    buf.emit_u32(0x97FFFFEA);              // BL #-22

    // 005C: sub x29, x29, #24             ; frame restore
    buf.emit_u32(0xD10063BD);              // SUB X29, X29, #0x18

    // 0060: ldr w10, [x29, #4]            ; reload local.a
    buf.emit_u32(0xB94007AA);              // LDR W10, [X29, #4]

    // 0064: add w9, w10, w9               ; result = a + b
    buf.emit_u32(0x0B090149);              // ADD W9, W10, W9

    // 0068: sub x21, x21, #1              ; fuel consume (return)
    buf.emit_u32(0xD10004B5);              // SUB X21, X21, #1

    // 006C: ldr x30, [sp], #16            ; epilogue — restore LR
    buf.emit_u32(0xF84107FE);              // LDR X30, [SP], #16

    // 0070: ret
    buf.emit_u32(0xD65F03C0);

    // --- suspend_0 stub (at 0x74) ---
    // For this test we don't actually suspend — just return.
    // In the real runtime, this would materialize frame state.

    // 0074: ldr x30, [sp], #16
    buf.emit_u32(0xF84107FE);
    // 0078: ret
    buf.emit_u32(0xD65F03C0);

    // --- suspend_1 stub (at 0x80, but we said 0x8C above) ---
    // Actually let me recalculate. suspend_0 is at 0x74 (2 words = 0x74, 0x78).
    // So suspend_1 needs to start at the right place.
    // Let's pad to make suspend_1 land at 0x8C.
    // Current position after suspend_0: 0x7C
    // Need to get to 0x8C: that's 4 words of padding (0x7C, 0x80, 0x84, 0x88)
    buf.emit_u32(0xD4200000); // brk #0 (padding)
    buf.emit_u32(0xD4200000);
    buf.emit_u32(0xD4200000);
    buf.emit_u32(0xD4200000);

    // 008C: suspend_1 stub
    buf.emit_u32(0xF84107FE); // ldr x30, [sp], #16
    buf.emit_u32(0xD65F03C0); // ret

    let fib_end = buf.len();
    let _ = fib_end;

    // --- Entry trampoline ---
    // Sets up the register convention and calls fib.
    // This is what the host calls via C ABI.
    //
    // Args (C ABI):
    //   x0 = n (i32 param)
    //   x1 = pointer to locals frame (we use as x29)
    //   x2 = initial fuel
    //
    // We set up: x9 = n, x29 = locals base, x21 = fuel, then call fib.
    // On return: x0 = result (from w9), x1 = remaining fuel (from x21).

    let trampoline_offset = buf.len();

    // Save callee-saved regs we clobber
    buf.emit_u32(0xA9BE7BFD); // stp x29, x30, [sp, #-32]!
    buf.emit_u32(0xA90157F4); // stp x20, x21, [sp, #16]

    // Set up JIT registers
    buf.emit_u32(0xAA0003E9); // mov x9, x0   (n → param reg)
    buf.emit_u32(0xAA0103FD); // mov x29, x1  (locals base)
    buf.emit_u32(0xAA0203F5); // mov x21, x2  (fuel)

    // Call fib (offset from here to fib_offset)
    let call_word_idx = buf.len() / 4;
    let fib_word_idx = fib_offset / 4;
    let bl_offset = (fib_word_idx as i32) - (call_word_idx as i32);
    let bl_imm26 = (bl_offset as u32) & 0x03FF_FFFF;
    buf.emit_u32(0x94000000 | bl_imm26); // bl fib

    // Move results to C ABI return regs
    buf.emit_u32(0x2A0903E0); // mov w0, w9   (result)
    buf.emit_u32(0xAA1503E1); // mov x1, x21  (remaining fuel)

    // Restore callee-saved regs
    buf.emit_u32(0xA94157F4); // ldp x20, x21, [sp, #16]
    buf.emit_u32(0xA8C27BFD); // ldp x29, x30, [sp], #32

    buf.emit_u32(0xD65F03C0); // ret

    buf.finalize().unwrap();

    // Allocate a locals frame (24 bytes, zeroed)
    let mut frame = [0u8; 64];
    let frame_ptr = frame.as_mut_ptr();

    let trampoline_ptr = unsafe { buf.entry().add(trampoline_offset) };
    let func: unsafe extern "C" fn(i32, *mut u8, i64) -> (i32, i64) =
        unsafe { core::mem::transmute(trampoline_ptr) };

    let (result, _fuel) = unsafe { func(10, frame_ptr, 10_000) };
    assert_eq!(result, 55, "fib(10) should be 55, got {result}");

    let (result, _fuel) = unsafe { func(0, frame_ptr, 10_000) };
    assert_eq!(result, 0, "fib(0) should be 0, got {result}");

    let (result, _fuel) = unsafe { func(1, frame_ptr, 10_000) };
    assert_eq!(result, 1, "fib(1) should be 1, got {result}");

    let (result, _fuel) = unsafe { func(20, frame_ptr, 100_000) };
    assert_eq!(result, 6765, "fib(20) should be 6765, got {result}");
}
