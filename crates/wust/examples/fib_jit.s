// Hand-written fib(n) for aarch64 — reference implementations for benchmarking.
//
// Each variant implements the same recursive fibonacci algorithm with
// different calling conventions and frame layouts. Naming matches the
// Rust extern declarations 1:1 (minus the leading underscore).
//
// Label scheme (numeric labels required by MachO for conditional branches):
//   0x = fib_asm          (0 = base)
//   1x = fib_asm_fuel     (10 = recurse, 11 = base, 12 = oof)
//   2x = fib_asm_jit      (20 = recurse, 29 = oof)
//   3x = fib_asm_jit_frame16       (30 = recurse, 39 = oof)
//   4x = fib_asm_jit_frame16_hdr   (40 = recurse, 49 = oof)

.text
.align 4

// ============================================================
// asm: Pure recursive fibonacci, C calling convention, no fuel.
//
// Uses callee-saved registers (x19, x20) to hold `n` and
// `fib(n-1)` across calls — no frame spills needed.
// This is the theoretical best a native compiler can do.
//
// Calling convention: w0 = n, returns i32 in w0.
// ============================================================
.global _fib_asm
_fib_asm:
    cmp     w0, #1
    b.le    0f                          // → base

    stp     x29, x30, [sp, #-32]!
    mov     x29, sp
    stp     x19, x20, [sp, #16]

    mov     w19, w0
    sub     w0, w0, #1
    bl      _fib_asm
    mov     w20, w0

    sub     w0, w19, #2
    bl      _fib_asm
    add     w0, w0, w20

    ldp     x19, x20, [sp, #16]
    ldp     x29, x30, [sp], #32
0: // base
    ret

// ============================================================
// asm+fuel: Fuel check at every wasm opcode boundary.
//
// Uses callee-saved registers (x21, x22) like the native variant.
// x24 = pinned fuel counter (decremented before each op).
// When fuel runs out, returns -1.
//
// Calling convention: w0 = n, returns i32 in w0.
// ============================================================
.global _fib_asm_fuel
.global _fib_asm_fuel_entry

_fib_asm_fuel:
    stp     x29, x30, [sp, #-0x10]!
    stp     x21, x22, [sp, #-0x10]!
    mov     x29, sp
    mov     w22, w0

    subs    x24, x24, #1
    b.le    12f                         // → oof
    cmp     w22, #1
    b.le    11f                         // → base

    // fib(n-1)
    subs    x24, x24, #2
    b.le    12f                         // → oof
    sub     w0, w22, #1
    bl      _fib_asm_fuel
    mov     w21, w0

    // fib(n-2)
    subs    x24, x24, #2
    b.le    12f                         // → oof
    sub     w0, w22, #2
    bl      _fib_asm_fuel

    // fib(n-1) + fib(n-2)
    subs    x24, x24, #2
    b.le    12f                         // → oof
    add     w0, w21, w0

    ldp     x21, x22, [sp], #0x10
    ldp     x29, x30, [sp], #0x10
    ret

11: // base
    subs    x24, x24, #1
    b.le    12f                         // → oof
    mov     w0, w22
    ldp     x21, x22, [sp], #0x10
    ldp     x29, x30, [sp], #0x10
    ret

12: // oof
    mov     w0, #-1
    ldp     x21, x22, [sp], #0x10
    ldp     x29, x30, [sp], #0x10
    ret

.align 4
_fib_asm_fuel_entry:
    stp     x29, x30, [sp, #-0x10]!
    str     x24, [sp, #-0x10]!
    mov     x29, sp
    mov     x24, x1
    bl      _fib_asm_fuel
    ldr     x24, [sp], #0x10
    ldp     x29, x30, [sp], #0x10
    ret

// ============================================================
// asm+jit: JIT calling convention, old frame layout.
//
// No callee-saved registers — locals live in the wasm frame,
// reloaded from memory after each call.
//
// Register convention:
//   x21 = pinned fuel, x29 = wasm fp, x9-x15 = scratch.
//   Args in x9, result in x9. x30 on native stack.
//
// Frame layout (locals at +0):
//   [x29 + 0]  = local 0 (n)
//   [x29 + 8]  = local 1 (a)
//   [x29 + 16] = local 2 (b)
//   Frame advance = 48 bytes.
// ============================================================
.global _fib_asm_jit
.global _fib_asm_jit_entry

_fib_asm_jit:
    str     x30, [sp, #-16]!
    str     x9, [x29, #0]              // local.n = param

    cmp     w9, #1
    b.gt    20f                         // → recurse

    // base
    subs    x21, x21, #1
    b.le    29f                         // → oof
    ldr     x30, [sp], #16
    ret

20: // recurse
    sub     w10, w9, #1
    subs    x21, x21, #2
    b.le    29f                         // → oof

    // fib(n-1)
    mov     x9, x10
    add     x29, x29, #48
    bl      _fib_asm_jit
    sub     x29, x29, #48
    str     x9, [x29, #8]              // local.a = fib(n-1)

    ldr     x9, [x29, #0]
    sub     w9, w9, #2
    subs    x21, x21, #2
    b.le    29f                         // → oof

    // fib(n-2)
    add     x29, x29, #48
    bl      _fib_asm_jit
    sub     x29, x29, #48
    str     x9, [x29, #16]             // local.b = fib(n-2)

    // fib(n-1) + fib(n-2)
    ldr     x9, [x29, #8]
    ldr     x10, [x29, #16]
    add     w9, w9, w10
    subs    x21, x21, #1
    b.le    29f                         // → oof

    ldr     x30, [sp], #16
    ret

29: // oof
    mov     w9, #-1
    ldr     x30, [sp], #16
    ret

.align 4
_fib_asm_jit_entry:
    stp     x29, x30, [sp, #-16]!
    stp     x20, x21, [sp, #-16]!
    sub     sp, sp, #0x10000
    add     x29, sp, #0
    mov     x21, x1
    mov     w9, w0
    bl      _fib_asm_jit
    mov     w0, w9
    add     sp, sp, #0x10000
    ldp     x20, x21, [sp], #16
    ldp     x29, x30, [sp], #16
    ret

// ============================================================
// asm+jit+frame16: JIT calling convention, new frame layout.
//
// Same as asm+jit but locals shifted by +16 bytes to reserve
// space for the frame header (prev_fp + func_idx|wasm_pc).
// Header slots NOT written here — deferred to cold suspend path.
//
// Frame layout:
//   [x29 + 0]  = prev_fp      (reserved)
//   [x29 + 8]  = header        (reserved)
//   [x29 + 16] = local 0 (n)
//   [x29 + 24] = local 1 (a)
//   [x29 + 32] = local 2 (b)
//   Frame advance = 40 bytes.
// ============================================================
.global _fib_asm_jit_frame16
.global _fib_asm_jit_frame16_entry

_fib_asm_jit_frame16:
    str     x30, [sp, #-16]!
    str     x9, [x29, #16]             // local.n = param (+16)

    cmp     w9, #1
    b.gt    30f                         // → recurse

    // base
    subs    x21, x21, #1
    b.le    39f                         // → oof
    ldr     x30, [sp], #16
    ret

30: // recurse
    sub     w10, w9, #1
    subs    x21, x21, #2
    b.le    39f                         // → oof

    // fib(n-1)
    mov     x9, x10
    add     x29, x29, #40
    bl      _fib_asm_jit_frame16
    sub     x29, x29, #40
    str     x9, [x29, #24]             // local.a = fib(n-1)

    ldr     x9, [x29, #16]
    sub     w9, w9, #2
    subs    x21, x21, #2
    b.le    39f                         // → oof

    // fib(n-2)
    add     x29, x29, #40
    bl      _fib_asm_jit_frame16
    sub     x29, x29, #40
    str     x9, [x29, #32]             // local.b = fib(n-2)

    // fib(n-1) + fib(n-2)
    ldr     x9, [x29, #24]
    ldr     x10, [x29, #32]
    add     w9, w9, w10
    subs    x21, x21, #1
    b.le    39f                         // → oof

    ldr     x30, [sp], #16
    ret

39: // oof
    mov     w9, #-1
    ldr     x30, [sp], #16
    ret

.align 4
_fib_asm_jit_frame16_entry:
    stp     x29, x30, [sp, #-16]!
    stp     x20, x21, [sp, #-16]!
    sub     sp, sp, #0x10000
    add     x29, sp, #0
    mov     x21, x1
    mov     w9, w0
    bl      _fib_asm_jit_frame16
    mov     w0, w9
    add     sp, sp, #0x10000
    ldp     x20, x21, [sp], #16
    ldp     x29, x30, [sp], #16
    ret

// ============================================================
// asm+jit+frame16+hdr: Same as frame16 but writes the frame
// header in the recursive path (deferred past base case check).
//
// All frame stores (header, local.n, zeros) are deferred to the
// recursive branch — the base case only saves/restores lr.
// ============================================================
.global _fib_asm_jit_frame16_hdr
.global _fib_asm_jit_frame16_hdr_entry

_fib_asm_jit_frame16_hdr:
    str     x30, [sp, #-16]!

    cmp     w9, #1
    b.gt    40f                         // → recurse

    // base
    subs    x21, x21, #1
    b.le    49f                         // → oof
    ldr     x30, [sp], #16
    ret

40: // recurse
    movz    x0, #0
    str     x0, [x29, #8]              // header = func_idx | wasm_pc
    str     x9, [x29, #16]             // local.n
    sub     w10, w9, #1
    subs    x21, x21, #2
    b.le    49f                         // → oof

    // fib(n-1)
    mov     x9, x10
    add     x29, x29, #40
    bl      _fib_asm_jit_frame16_hdr
    sub     x29, x29, #40
    str     x9, [x29, #24]             // local.a = fib(n-1)

    ldr     x9, [x29, #16]
    sub     w9, w9, #2
    subs    x21, x21, #2
    b.le    49f                         // → oof

    // fib(n-2)
    add     x29, x29, #40
    bl      _fib_asm_jit_frame16_hdr
    sub     x29, x29, #40
    str     x9, [x29, #32]             // local.b = fib(n-2)

    // fib(n-1) + fib(n-2)
    ldr     x9, [x29, #24]
    ldr     x10, [x29, #32]
    add     w9, w9, w10
    subs    x21, x21, #1
    b.le    49f                         // → oof

    ldr     x30, [sp], #16
    ret

49: // oof
    mov     w9, #-1
    ldr     x30, [sp], #16
    ret

.align 4
_fib_asm_jit_frame16_hdr_entry:
    stp     x29, x30, [sp, #-16]!
    stp     x20, x21, [sp, #-16]!
    sub     sp, sp, #0x10000
    add     x29, sp, #0
    mov     x21, x1
    mov     w9, w0
    bl      _fib_asm_jit_frame16_hdr
    mov     w0, w9
    add     sp, sp, #0x10000
    ldp     x20, x21, [sp], #16
    ldp     x29, x30, [sp], #16
    ret
