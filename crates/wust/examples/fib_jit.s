// Hand-written fib for aarch64 — reference implementations for benchmarking.
//
// All follow C calling convention: w0 = n, returns i32 in w0.
// Fuel variants: x1 = initial fuel count (or pointer for calls-only).

.text
.align 4

// ============================================================
// No fuel check — pure recursive, no overhead.
// ============================================================
.global _fib_asm_no_fuel
_fib_asm_no_fuel:
    cmp     w0, #1
    b.le    0f
    stp     x29, x30, [sp, #-32]!
    mov     x29, sp
    stp     x19, x20, [sp, #16]
    mov     w19, w0
    sub     w0, w0, #1
    bl      _fib_asm_no_fuel
    mov     w20, w0
    sub     w0, w19, #2
    bl      _fib_asm_no_fuel
    add     w0, w0, w20
    ldp     x19, x20, [sp, #16]
    ldp     x29, x30, [sp], #32
0:
    ret

// ============================================================
// Fuel check at call sites only.
// x1 = *fuel (preserved in x21 across calls).
// ============================================================
.global _fib_asm_fuel_calls
_fib_asm_fuel_calls:
    cmp     w0, #1
    b.le    0f
    stp     x29, x30, [sp, #-48]!
    mov     x29, sp
    stp     x19, x20, [sp, #16]
    str     x21, [sp, #32]
    mov     x21, x1
    mov     w19, w0

    // fuel check before call 1
    ldr     x2, [x21]
    subs    x2, x2, #1
    str     x2, [x21]
    b.mi    1f

    sub     w0, w19, #1
    mov     x1, x21
    bl      _fib_asm_fuel_calls
    mov     w20, w0

    // fuel check before call 2
    ldr     x2, [x21]
    subs    x2, x2, #1
    str     x2, [x21]
    b.mi    1f

    sub     w0, w19, #2
    mov     x1, x21
    bl      _fib_asm_fuel_calls
    add     w0, w0, w20

    ldr     x21, [sp, #32]
    ldp     x19, x20, [sp, #16]
    ldp     x29, x30, [sp], #48
0:
    ret
1:  // trap
    mov     w0, #-1
    ldr     x21, [sp, #32]
    ldp     x19, x20, [sp, #16]
    ldp     x29, x30, [sp], #48
    ret

// ============================================================
// Fuel check at every wasm instruction boundary.
// x24 = pinned fuel register (pure register, no memory traffic).
// ============================================================
.global _fib_asm_fuel_all
.global _fib_asm_fuel_all_entry

_fib_asm_fuel_all:
    stp     x29, x30, [sp, #-0x10]!
    stp     x21, x22, [sp, #-0x10]!
    mov     x29, sp
    mov     w22, w0                    // n in callee-saved

    // wasm: local.get 0 / i32.const 1 / i32.le_s / if
    subs    x24, x24, #1
    b.le    2f
    cmp     w22, #1
    b.le    3f

    // wasm: local.get 0 / i32.const 1 / i32.sub
    subs    x24, x24, #1
    b.le    2f
    sub     w0, w22, #1

    // wasm: call $fib
    subs    x24, x24, #1
    b.le    2f
    bl      _fib_asm_fuel_all
    mov     w21, w0                    // save fib(n-1)

    // wasm: local.get 0 / i32.const 2 / i32.sub
    subs    x24, x24, #1
    b.le    2f
    sub     w0, w22, #2

    // wasm: call $fib
    subs    x24, x24, #1
    b.le    2f
    bl      _fib_asm_fuel_all          // w0 = fib(n-2)

    // wasm: local.get 1 / local.get 2 / i32.add
    subs    x24, x24, #1
    b.le    2f
    add     w0, w21, w0

    // wasm: end (function return)
    subs    x24, x24, #1
    b.le    2f

    ldp     x21, x22, [sp], #0x10
    ldp     x29, x30, [sp], #0x10
    ret

3:  // base case: local.get $n / return
    subs    x24, x24, #1
    b.le    2f
    mov     w0, w22

    ldp     x21, x22, [sp], #0x10
    ldp     x29, x30, [sp], #0x10
    ret

2:  // out of fuel
    mov     w0, #-1
    ldp     x21, x22, [sp], #0x10
    ldp     x29, x30, [sp], #0x10
    ret

// C-callable wrapper: x1 = initial fuel value -> pinned into x24.
.align 4
_fib_asm_fuel_all_entry:
    stp     x29, x30, [sp, #-0x10]!
    str     x24, [sp, #-0x10]!
    mov     x29, sp
    mov     x24, x1
    bl      _fib_asm_fuel_all
    ldr     x24, [sp], #0x10
    ldp     x29, x30, [sp], #0x10
    ret

// ============================================================
// Custom calling convention — wasm-managed stack.
//
// x23 = wasm stack pointer (caller-managed, flat array)
// x24 = pinned fuel register
// ============================================================
.global _fib_asm_wasm_stack
.global _fib_asm_wasm_stack_entry

_fib_asm_wasm_stack:
    // On entry: arg n is at [x23 - 4], as i32
    ldr     w9, [x23, #-4]            // w9 = n

    // fuel: local.get 0 / i32.const 1 / i32.le_s / if
    subs    x24, x24, #1
    b.le    32f
    cmp     w9, #1
    b.le    33f

    // --- recursive case ---

    // Save return address on native stack (only mandatory thing)
    str     x30, [sp, #-0x10]!

    // Caller saves local 0 (n) to wasm stack, pushes arg (n-1)
    subs    x24, x24, #1
    b.le    34f
    sub     w10, w9, #1
    stp     w9, w10, [x23], #8        // push local0 + arg, x23 += 8

    // call fib(n-1)
    subs    x24, x24, #1
    b.le    34f
    bl      _fib_asm_wasm_stack

    // Result is at [x23 - 4]. Push arg (n-2) on top.
    subs    x24, x24, #1
    b.le    34f
    ldr     w9, [x23, #-8]            // reload n from wasm stack
    sub     w10, w9, #2
    str     w10, [x23], #4            // push arg n-2, x23 += 4

    // call fib(n-2)
    subs    x24, x24, #1
    b.le    34f
    bl      _fib_asm_wasm_stack

    // Result at [x23 - 4] = fib(n-2)
    subs    x24, x24, #1
    b.le    34f
    ldp     w11, w12, [x23, #-8]      // w11 = fib(n-1), w12 = fib(n-2)
    add     w0, w11, w12

    // Pop wasm stack, write result to caller's arg slot
    sub     x23, x23, #12
    str     w0, [x23, #-4]

    // Restore return address
    ldr     x30, [sp], #0x10
    ret

33: // base case: fib(n) = n when n <= 1
    subs    x24, x24, #1
    b.le    32f
    // result = n, already at [x23 - 4], nothing to do
    ret

32: // out of fuel
    mov     w0, #-1
    str     w0, [x23, #-4]
    ret

34: // out of fuel (mid-recursion, native stack has x30)
    mov     w0, #-1
    str     w0, [x23, #-4]
    ldr     x30, [sp], #0x10
    ret

// ============================================================
// Fuel + jump table trampoline for calls.
//
// Instead of loading a function pointer from memory and doing
// `blr` (indirect call), callers do `bl <trampoline>` (direct).
// The trampoline is a single `b <target>` instruction.
//
// Call overhead: 1 extra `b` hop vs 2 `ldr` + `blr`.
// x24 = pinned fuel register.
// ============================================================
.global _fib_asm_jumptable
.global _fib_asm_jumptable_entry

// Jump table — one `b` per function. For fib we have one function.
.align 4
_fib_jumptable:
    b       _fib_asm_jumptable          // func 0: fib

_fib_asm_jumptable:
    stp     x29, x30, [sp, #-0x10]!
    stp     x21, x22, [sp, #-0x10]!
    mov     x29, sp
    mov     w22, w0                     // n in callee-saved

    // wasm: local.get 0 / i32.const 1 / i32.le_s / if
    subs    x24, x24, #1
    b.le    42f
    cmp     w22, #1
    b.le    43f

    // wasm: local.get 0 / i32.const 1 / i32.sub
    subs    x24, x24, #1
    b.le    42f
    sub     w0, w22, #1

    // wasm: call $fib — via jump table trampoline
    subs    x24, x24, #1
    b.le    42f
    bl      _fib_jumptable              // bl to trampoline (direct), which does b to target
    mov     w21, w0                     // save fib(n-1)

    // wasm: local.get 0 / i32.const 2 / i32.sub
    subs    x24, x24, #1
    b.le    42f
    sub     w0, w22, #2

    // wasm: call $fib — via jump table trampoline
    subs    x24, x24, #1
    b.le    42f
    bl      _fib_jumptable              // w0 = fib(n-2)

    // wasm: local.get 1 / local.get 2 / i32.add
    subs    x24, x24, #1
    b.le    42f
    add     w0, w21, w0

    // wasm: end (function return)
    subs    x24, x24, #1
    b.le    42f

    ldp     x21, x22, [sp], #0x10
    ldp     x29, x30, [sp], #0x10
    ret

43: // base case: local.get $n / return
    subs    x24, x24, #1
    b.le    42f
    mov     w0, w22

    ldp     x21, x22, [sp], #0x10
    ldp     x29, x30, [sp], #0x10
    ret

42: // out of fuel
    mov     w0, #-1
    ldp     x21, x22, [sp], #0x10
    ldp     x29, x30, [sp], #0x10
    ret

// C-callable wrapper: x1 = initial fuel value -> pinned into x24.
.align 4
_fib_asm_jumptable_entry:
    stp     x29, x30, [sp, #-0x10]!
    str     x24, [sp, #-0x10]!
    mov     x29, sp
    mov     x24, x1
    bl      _fib_jumptable              // enter via trampoline
    ldr     x24, [sp], #0x10
    ldp     x29, x30, [sp], #0x10
    ret

// ============================================================
// JIT-style with frame locals + fuel, mimics our actual JIT output.
// x21 = pinned fuel register.
// x29 = locals frame pointer.
// x20 = context (unused here, just reserved).
// x9-x15 = scratch (caller-saved).
// Args in x9, result in x9.
//
// "reload" variant: reloads local.n from frame even when x9
// still holds it (matches current JIT codegen).
// ============================================================
.global _fib_jit_reload
.global _fib_jit_reload_entry

_fib_jit_reload:
    str     x30, [sp, #-16]!           // save lr
    str     x9, [x29, #0]              // stack[fp+0] = local.n
    str     xzr, [x29, #8]             // stack[fp+1] = local.a = 0
    str     xzr, [x29, #16]            // stack[fp+2] = local.b = 0

    // --- cmp + branch (reload from frame) ---
    ldr     x9, [x29, #0]              // reload local.n  ← UNNECESSARY
    cmp     w9, #1
    b.gt    50f

    // base case
    subs    x21, x21, #1
    b.le    59f
    ldr     x9, [x29, #0]              // reload local.n  ← UNNECESSARY
    ldr     x30, [sp], #16
    ret

50: // recursive case
    ldr     x10, [x29, #0]             // reload local.n  ← UNNECESSARY
    sub     w10, w10, #1               // x10 = n - 1
    subs    x21, x21, #1
    b.le    59f
    subs    x21, x21, #1
    b.le    59f

    mov     x9, x10                    // arg = n-1
    add     x29, x29, #48              // advance fp
    bl      _fib_jit_reload
    sub     x29, x29, #48              // restore fp
    str     x9, [x29, #8]              // local.a = result

    ldr     x9, [x29, #0]              // reload local.n (clobbered by call)
    sub     w9, w9, #2                 // x9 = n - 2
    subs    x21, x21, #1
    b.le    59f
    subs    x21, x21, #1
    b.le    59f

    add     x29, x29, #48
    bl      _fib_jit_reload
    sub     x29, x29, #48
    str     x9, [x29, #16]             // local.b = result

    ldr     x9, [x29, #8]              // reload local.a
    ldr     x10, [x29, #16]            // reload local.b
    add     w9, w9, w10                // x9 = a + b
    subs    x21, x21, #1
    b.le    59f

    ldr     x30, [sp], #16
    ret

59: // out of fuel
    mov     w9, #-1
    ldr     x30, [sp], #16
    ret

// ============================================================
// Same as above but avoids unnecessary reloads.
// x9 is kept live from the param store — no reload before cmp
// or first sub.
// ============================================================
.global _fib_jit_norld
.global _fib_jit_norld_entry

_fib_jit_norld:
    str     x30, [sp, #-16]!           // save lr
    str     x9, [x29, #0]              // stack[fp+0] = local.n
    str     xzr, [x29, #8]             // stack[fp+1] = local.a = 0
    str     xzr, [x29, #16]            // stack[fp+2] = local.b = 0

    // --- cmp + branch (x9 still has n!) ---
    cmp     w9, #1                      // no reload needed
    b.gt    60f

    // base case: x9 = n, just return it
    subs    x21, x21, #1
    b.le    69f
    ldr     x30, [sp], #16
    ret

60: // recursive case
    sub     w10, w9, #1                 // x10 = n - 1 (x9 still live!)
    subs    x21, x21, #1
    b.le    69f
    subs    x21, x21, #1
    b.le    69f

    mov     x9, x10                    // arg = n-1
    add     x29, x29, #48
    bl      _fib_jit_norld
    sub     x29, x29, #48
    str     x9, [x29, #8]              // local.a = result

    ldr     x9, [x29, #0]              // reload local.n (clobbered by call — necessary!)
    sub     w9, w9, #2                 // x9 = n - 2
    subs    x21, x21, #1
    b.le    69f
    subs    x21, x21, #1
    b.le    69f

    add     x29, x29, #48
    bl      _fib_jit_norld
    sub     x29, x29, #48
    str     x9, [x29, #16]             // local.b = result

    ldr     x9, [x29, #8]              // reload local.a
    ldr     x10, [x29, #16]            // reload local.b
    add     w9, w9, w10                // x9 = a + b
    subs    x21, x21, #1
    b.le    69f

    ldr     x30, [sp], #16
    ret

69: // out of fuel
    mov     w9, #-1
    ldr     x30, [sp], #16
    ret

// C-callable wrappers
.align 4
_fib_jit_reload_entry:
    stp     x29, x30, [sp, #-16]!
    stp     x20, x21, [sp, #-16]!
    // allocate frame space (48 bytes per frame × ~30 depth = ~1440, use 64K)
    sub     sp, sp, #0x10000
    add     x29, sp, #0                 // fp = base of frame area
    mov     x21, x1                     // fuel
    mov     w9, w0                      // arg in x9
    bl      _fib_jit_reload
    mov     w0, w9                      // result to w0
    add     sp, sp, #0x10000
    ldp     x20, x21, [sp], #16
    ldp     x29, x30, [sp], #16
    ret

.align 4
_fib_jit_norld_entry:
    stp     x29, x30, [sp, #-16]!
    stp     x20, x21, [sp, #-16]!
    sub     sp, sp, #0x10000
    add     x29, sp, #0
    mov     x21, x1
    mov     w9, w0
    bl      _fib_jit_norld
    mov     w0, w9
    add     sp, sp, #0x10000
    ldp     x20, x21, [sp], #16
    ldp     x29, x30, [sp], #16
    ret

// C-callable entry: w0 = n, x1 = fuel, x2 = wasm stack base
.align 4
_fib_asm_wasm_stack_entry:
    stp     x29, x30, [sp, #-0x10]!
    stp     x23, x24, [sp, #-0x10]!
    mov     x29, sp
    mov     x23, x2                    // wasm stack pointer
    mov     x24, x1                    // fuel
    // Push arg onto wasm stack
    str     w0, [x23], #4             // push n, x23 += 4
    bl      _fib_asm_wasm_stack
    // Result at [x23 - 4]
    ldr     w0, [x23, #-4]
    ldp     x23, x24, [sp], #0x10
    ldp     x29, x30, [sp], #0x10
    ret
