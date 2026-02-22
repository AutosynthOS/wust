// Hand-compiled fib for aarch64 — simulates JIT output.
// Four variants: no fuel, fuel at calls, fuel at every op, tail-call.
//
// All follow C calling convention: w0 = n, returns i32 in w0.
// Fuel variants: x1 = initial fuel count (or pointer for calls-only).

.text
.align 4

// ============================================================
// Variant 1: No fuel check
// ============================================================
.global _fib_jit_no_fuel
_fib_jit_no_fuel:
    cmp     w0, #1
    b.le    0f
    stp     x29, x30, [sp, #-32]!
    mov     x29, sp
    stp     x19, x20, [sp, #16]
    mov     w19, w0
    sub     w0, w0, #1
    bl      _fib_jit_no_fuel
    mov     w20, w0
    sub     w0, w19, #2
    bl      _fib_jit_no_fuel
    add     w0, w0, w20
    ldp     x19, x20, [sp, #16]
    ldp     x29, x30, [sp], #32
0:
    ret

// ============================================================
// Variant 2: Fuel check at call sites only
// x1 = *fuel (preserved in x21 across calls)
// ============================================================
.global _fib_jit_fuel_calls
_fib_jit_fuel_calls:
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
    bl      _fib_jit_fuel_calls
    mov     w20, w0

    // fuel check before call 2
    ldr     x2, [x21]
    subs    x2, x2, #1
    str     x2, [x21]
    b.mi    1f

    sub     w0, w19, #2
    mov     x1, x21
    bl      _fib_jit_fuel_calls
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
// Variant 3: Fuel check at every real wasm instruction boundary
// x24 = pinned fuel register (pure register, no memory traffic).
// Based on actual Cranelift-style output.
// ============================================================
.global _fib_jit_fuel_all
.global _fib_jit_fuel_all_entry

_fib_jit_fuel_all:
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
    bl      _fib_jit_fuel_all
    mov     w21, w0                    // save fib(n-1)

    // wasm: local.get 0 / i32.const 2 / i32.sub
    subs    x24, x24, #1
    b.le    2f
    sub     w0, w22, #2

    // wasm: call $fib
    subs    x24, x24, #1
    b.le    2f
    bl      _fib_jit_fuel_all          // w0 = fib(n-2)

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

// C-callable wrapper: x1 = initial fuel value → pinned into x24.
.align 4
_fib_jit_fuel_all_entry:
    stp     x29, x30, [sp, #-0x10]!
    str     x24, [sp, #-0x10]!
    mov     x29, sp
    mov     x24, x1
    bl      _fib_jit_fuel_all
    ldr     x24, [sp], #0x10
    ldp     x29, x30, [sp], #0x10
    ret

// ============================================================
// Variant 5: Fuel@op + EAGER stores (worst case)
// x24 = pinned fuel, x23 = locals base pointer.
// After every op, stores live registers back to locals memory.
// This simulates "always clean state" — maximum store overhead.
// ============================================================
.global _fib_jit_fuel_eager
.global _fib_jit_fuel_eager_entry

_fib_jit_fuel_eager:
    stp     x29, x30, [sp, #-0x10]!
    stp     x21, x22, [sp, #-0x10]!
    str     x23, [sp, #-0x10]!
    // Allocate locals area on stack: 3 locals * 4 bytes = 12, padded to 16
    sub     sp, sp, #16
    mov     x29, sp
    mov     x23, sp                    // x23 = locals base
    mov     w22, w0
    str     w22, [x23, #0]            // locals[0] = n

    // wasm: local.get 0 / i32.const 1 / i32.le_s / if
    subs    x24, x24, #1
    b.le    12f
    cmp     w22, #1
    b.le    13f

    // wasm: local.get 0 / i32.const 1 / i32.sub
    subs    x24, x24, #1
    b.le    12f
    sub     w0, w22, #1

    // wasm: call $fib
    subs    x24, x24, #1
    b.le    12f
    bl      _fib_jit_fuel_eager
    mov     w21, w0
    str     w21, [x23, #4]            // eager store: locals[1] = fib(n-1)

    // wasm: local.get 0 / i32.const 2 / i32.sub
    subs    x24, x24, #1
    b.le    12f
    sub     w0, w22, #2

    // wasm: call $fib
    subs    x24, x24, #1
    b.le    12f
    bl      _fib_jit_fuel_eager
    str     w0, [x23, #8]             // eager store: locals[2] = fib(n-2)

    // wasm: local.get 1 / local.get 2 / i32.add
    subs    x24, x24, #1
    b.le    12f
    ldr     w21, [x23, #4]            // eager load: must re-read from memory
    ldr     w2, [x23, #8]             // eager load
    add     w0, w21, w2

    // wasm: end
    subs    x24, x24, #1
    b.le    12f

    add     sp, sp, #16
    ldr     x23, [sp], #0x10
    ldp     x21, x22, [sp], #0x10
    ldp     x29, x30, [sp], #0x10
    ret

13: // base case
    subs    x24, x24, #1
    b.le    12f
    mov     w0, w22

    add     sp, sp, #16
    ldr     x23, [sp], #0x10
    ldp     x21, x22, [sp], #0x10
    ldp     x29, x30, [sp], #0x10
    ret

12: // out of fuel
    mov     w0, #-1
    add     sp, sp, #16
    ldr     x23, [sp], #0x10
    ldp     x21, x22, [sp], #0x10
    ldp     x29, x30, [sp], #0x10
    ret

.align 4
_fib_jit_fuel_eager_entry:
    stp     x29, x30, [sp, #-0x10]!
    stp     x23, x24, [sp, #-0x10]!
    mov     x29, sp
    mov     x24, x1
    bl      _fib_jit_fuel_eager
    ldp     x23, x24, [sp], #0x10
    ldp     x29, x30, [sp], #0x10
    ret

// ============================================================
// Variant 6: Fuel@op + LAZY stores (realistic JIT)
// x24 = pinned fuel, x23 = locals base pointer.
// Stores only happen in the out-of-fuel path (cold, never taken).
// Hot path is pure registers — identical to variant 3.
// ============================================================
.global _fib_jit_fuel_lazy
.global _fib_jit_fuel_lazy_entry

_fib_jit_fuel_lazy:
    stp     x29, x30, [sp, #-0x10]!
    stp     x21, x22, [sp, #-0x10]!
    str     x23, [sp, #-0x10]!
    // Allocate locals area: 3 * 4 = 12 bytes, padded to 16
    sub     sp, sp, #16
    mov     x29, sp
    mov     x23, sp                    // x23 = locals base
    mov     w22, w0

    // wasm: local.get 0 / i32.const 1 / i32.le_s / if
    subs    x24, x24, #1
    b.le    22f                        // suspend point 0: locals[0]=w22
    cmp     w22, #1
    b.le    23f

    // wasm: local.get 0 / i32.const 1 / i32.sub
    subs    x24, x24, #1
    b.le    22f                        // suspend point 1: locals[0]=w22
    sub     w0, w22, #1

    // wasm: call $fib
    subs    x24, x24, #1
    b.le    22f                        // suspend point 2: locals[0]=w22
    bl      _fib_jit_fuel_lazy
    mov     w21, w0

    // wasm: local.get 0 / i32.const 2 / i32.sub
    subs    x24, x24, #1
    b.le    24f                        // suspend point 3: locals[0]=w22, locals[1]=w21
    sub     w0, w22, #2

    // wasm: call $fib
    subs    x24, x24, #1
    b.le    24f                        // suspend point 4: locals[0]=w22, locals[1]=w21
    bl      _fib_jit_fuel_lazy

    // wasm: local.get 1 / local.get 2 / i32.add
    subs    x24, x24, #1
    b.le    25f                        // suspend point 5: all three live
    add     w0, w21, w0

    // wasm: end
    subs    x24, x24, #1
    b.le    22f

    add     sp, sp, #16
    ldr     x23, [sp], #0x10
    ldp     x21, x22, [sp], #0x10
    ldp     x29, x30, [sp], #0x10
    ret

23: // base case
    subs    x24, x24, #1
    b.le    22f
    mov     w0, w22

    add     sp, sp, #16
    ldr     x23, [sp], #0x10
    ldp     x21, x22, [sp], #0x10
    ldp     x29, x30, [sp], #0x10
    ret

// --- Cold paths: lazy spill only on suspend ---
22: // suspend: only local 0 live
    str     w22, [x23, #0]
    mov     w0, #-1
    add     sp, sp, #16
    ldr     x23, [sp], #0x10
    ldp     x21, x22, [sp], #0x10
    ldp     x29, x30, [sp], #0x10
    ret

24: // suspend: locals 0 and 1 live
    stp     w22, w21, [x23, #0]
    mov     w0, #-1
    add     sp, sp, #16
    ldr     x23, [sp], #0x10
    ldp     x21, x22, [sp], #0x10
    ldp     x29, x30, [sp], #0x10
    ret

25: // suspend: locals 0, 1, 2 live (w0 = local 2)
    str     w22, [x23, #0]
    stp     w21, w0, [x23, #4]
    mov     w0, #-1
    add     sp, sp, #16
    ldr     x23, [sp], #0x10
    ldp     x21, x22, [sp], #0x10
    ldp     x29, x30, [sp], #0x10
    ret

.align 4
_fib_jit_fuel_lazy_entry:
    stp     x29, x30, [sp, #-0x10]!
    stp     x24, xzr, [sp, #-0x10]!
    mov     x29, sp
    mov     x24, x1
    bl      _fib_jit_fuel_lazy
    ldp     x24, xzr, [sp], #0x10
    ldp     x29, x30, [sp], #0x10
    ret

// ============================================================
// Variant 8: Custom calling convention — wasm-managed stack
//
// x23 = wasm stack pointer (caller-managed, flat array)
// x24 = pinned fuel register
//
// Convention:
//   - Caller pushes its live locals to [x23], bumps x23
//   - Caller pushes arg (n) to [x23]
//   - Callee reads arg from [x23 - 4], works in registers
//   - Callee writes i32 result to [x23 - 4] (overwrites arg)
//   - Caller restores x23, reads result
//   - Only x30 saved on native stack (for ret)
// ============================================================
.global _fib_jit_wasm_stack
.global _fib_jit_wasm_stack_entry

_fib_jit_wasm_stack:
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
    //   [x23 + 0] = n  (caller's live local)
    //   [x23 + 4] = n-1 (arg for callee)
    subs    x24, x24, #1
    b.le    34f
    sub     w10, w9, #1
    stp     w9, w10, [x23], #8        // push local0 + arg, x23 += 8

    // call fib(n-1)
    subs    x24, x24, #1
    b.le    34f
    bl      _fib_jit_wasm_stack

    // Result is at [x23 - 4]. Read it, store as local 1.
    // Now wasm stack: [x23-8]=saved_n, [x23-4]=fib(n-1)
    // We need saved_n to compute n-2, and fib(n-1) for the final add.
    // Push arg (n-2) on top:
    subs    x24, x24, #1
    b.le    34f
    ldr     w9, [x23, #-8]            // reload n from wasm stack
    sub     w10, w9, #2
    str     w10, [x23], #4            // push arg n-2, x23 += 4

    // call fib(n-2)
    subs    x24, x24, #1
    b.le    34f
    bl      _fib_jit_wasm_stack

    // Result at [x23 - 4] = fib(n-2)
    // [x23-12]=saved_n, [x23-8]=fib(n-1), [x23-4]=fib(n-2)
    subs    x24, x24, #1
    b.le    34f
    ldp     w11, w12, [x23, #-8]      // w11 = fib(n-1), w12 = fib(n-2)
    add     w0, w11, w12

    // Pop wasm stack: we pushed 12 bytes (8 + 4), go back to caller's frame
    // Caller had arg at [original_x23 - 4], we write result there
    sub     x23, x23, #12
    str     w0, [x23, #-4]            // overwrite caller's arg slot with result

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

// C-callable entry: w0 = n, x1 = fuel, x2 = wasm stack base
.align 4
_fib_jit_wasm_stack_entry:
    stp     x29, x30, [sp, #-0x10]!
    stp     x23, x24, [sp, #-0x10]!
    mov     x29, sp
    mov     x23, x2                    // wasm stack pointer
    mov     x24, x1                    // fuel
    // Push arg onto wasm stack
    str     w0, [x23], #4             // push n, x23 += 4
    bl      _fib_jit_wasm_stack
    // Result at [x23 - 4]
    ldr     w0, [x23, #-4]
    ldp     x23, x24, [sp], #0x10
    ldp     x29, x30, [sp], #0x10
    ret

// ============================================================
// Variant 7: Tail-call optimized (iterative accumulator)
//
// fib(n) = fib_iter(n, 0, 1)
// fib_iter(n, a, b) = if n == 0 then a else fib_iter(n-1, b, a+b)
//
// No stack frames, no calls — pure register loop.
// ============================================================
.global _fib_jit_tailcall
_fib_jit_tailcall:
    mov     w1, #0              // a = 0
    mov     w2, #1              // b = 1
0:
    cbz     w0, 1f              // if n == 0, return a
    add     w3, w1, w2          // tmp = a + b
    mov     w1, w2              // a = b
    mov     w2, w3              // b = tmp
    sub     w0, w0, #1          // n--
    b       0b
1:
    mov     w0, w1              // return a
    ret
