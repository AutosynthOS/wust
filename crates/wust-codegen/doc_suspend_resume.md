# Suspend/Resume Reference Example

## 1. Rust-ish pseudocode

```rust
/// If x <= 3, double it. Otherwise return as-is.
fn double_if_small(x: i32) -> i32 {
    if x <= 3 {
        x + x
    } else {
        x
    }
}

/// Sum double_if_small(i) for i from n down to 1.
fn sum_doubled(n: i32) -> i32 {
    let mut i = n;
    let mut acc = 0;
    loop {
        if i <= 0 {
            return acc;
        }
        acc = acc + double_if_small(i);
        i = i - 1;
    }
}
```

### Trace: `sum_doubled(4)`

```
sum_doubled(4)
  loop: i=4, acc=0   → double_if_small(4) = 4  → acc=4,  i=3
  loop: i=3, acc=4   → double_if_small(3) = 6  → acc=10, i=2
  loop: i=2, acc=10  → double_if_small(2) = 4  → acc=14, i=1
  loop: i=1, acc=14  → double_if_small(1) = 2  → acc=16, i=0
  loop: i=0, acc=16  → return 16
```

## 2. WAT

```wat
(module
  (func $double_if_small (export "double_if_small") (param $x i32) (result i32)
    (if (result i32) (i32.le_s (local.get $x) (i32.const 3))
      (then (i32.add (local.get $x) (local.get $x)))
      (else (local.get $x))
    )
  )

  (func $sum_doubled (export "sum_doubled") (param $n i32) (result i32)
    (local $i i32)
    (local $acc i32)
    (local.set $i (local.get $n))
    (block $done (result i32)
      (loop $again
        (br_if $done (i32.le_s (local.get $i) (i32.const 0)))
        (local.set $acc
          (i32.add (local.get $acc) (call $double_if_small (local.get $i))))
        (local.set $i (i32.sub (local.get $i) (i32.const 1)))
        (br $again)
      )
      (local.get $acc)
    )
  )
)
```

### Wasm concepts exercised

| Concept | Where |
|---|---|
| `if`/`else` with result type | `$double_if_small` — both arms produce an i32 |
| `loop` with backward `br` | `$again` in `$sum_doubled` |
| `block` with result type | `$done` carries `$acc` out of the loop |
| `br_if` conditional exit | exits loop when `i <= 0` |
| `call` inside a loop | `$sum_doubled` calls `$double_if_small` each iteration |
| Value live across a call | `$i` must survive the call to `$double_if_small` |

## 3. Block-argument SSA IR

Values flow through block parameters at branches — no phi nodes.
Each block declares its inputs. Each branch lists the values it passes.

```asm
func $double_if_small(v0: i32) -> i32:

    block_entry(v0: i32):
        v1 = iconst 3
        suspend_check suspend_s0(v0, v1)
        v2 = i32.le_s v0, v1
        suspend_check suspend_s1(v0, v2)
        br_if v2, block_then(v0), block_else(v0)

    block_then(v3: i32) -> (v4: i32):
        v4 = i32.add v3, v3
        suspend_check suspend_s2(v4)
        br block_merge(v4)

    block_else(v5: i32) -> (v6: i32):
        v6 = v5
        suspend_check suspend_s3(v6)
        br block_merge(v6)

    block_merge(v7: i32):
        return v7

    ;; --- suspend stubs ---
    suspend_s0(v0: i32, v1: i32):  todo
    suspend_s1(v0: i32, v2: i32):  todo
    suspend_s2(v4: i32):           todo
    suspend_s3(v6: i32):           todo


func $sum_doubled(v0: i32) -> i32:

    block_entry(v0: i32):
        v1 = iconst 0
        suspend_check suspend_s0(v0, v1)
        br loop_$again(v0, v1)

    loop_$again(v2: i32, v3: i32):              ;; v2=i, v3=acc
        v4 = iconst 0
        suspend_check suspend_s1(v2, v3, v4)
        v5 = i32.le_s v2, v4                    ;; i <= 0?
        suspend_check suspend_s2(v2, v3, v5)
        br_if v5, block_$done(v3)               ;; exit loop with acc
        ;; — still in the loop body —
        v6 = call $double_if_small(v2)
        suspend_check suspend_s3(v2, v3, v6)
        v7 = i32.add v3, v6                     ;; acc + double_if_small(i)
        suspend_check suspend_s4(v2, v7)
        v8 = iconst 1
        suspend_check suspend_s5(v2, v7, v8)
        v9 = i32.sub v2, v8                     ;; i - 1
        suspend_check suspend_s6(v7, v9)
        br loop_$again(v9, v7)                  ;; back-edge: loop(new_i, new_acc)

    block_$done(v10: i32):
        return v10

    ;; --- suspend stubs ---
    suspend_s0(v0: i32, v1: i32):              todo
    suspend_s1(v2: i32, v3: i32, v4: i32):    todo
    suspend_s2(v2: i32, v3: i32, v5: i32):    todo
    suspend_s3(v2: i32, v3: i32, v6: i32):    todo
    suspend_s4(v2: i32, v7: i32):              todo
    suspend_s5(v2: i32, v7: i32, v8: i32):    todo
    suspend_s6(v7: i32, v9: i32):              todo
```

Each `suspend_check` is a fuel decrement + conditional branch:
- **Hot path** (fuel > 0): fall through, continue executing.
- **Cold path** (fuel exhausted): branch to the corresponding `suspend_sN`
  stub, passing exactly the live vregs as arguments.

The suspend stubs receive the live state as block parameters. On resume,
they'll need to restore those values and jump back to the instruction
after the suspend point. For now they're just `todo` — the signature is
what matters.

### Reading the notation

- **`loop_$again(v2: i32, v3: i32):`** — a loop header block. Takes two
  params. On the back-edge `br loop_$again(v9, v7)`, the values v9 and v7
  become the next iteration's v2 and v3.

- **`block_then(v3: i32) -> (v4: i32):`** — a forward-only block. Takes
  v3 as input, produces v4 as output. The `-> (v4: i32)` labels the value
  that flows out via `br block_merge(v4)`.

- **`block_merge(v7: i32):`** — a merge point. Multiple predecessors
  (`block_then`, `block_else`) branch here, each passing one value. The
  block parameter v7 unifies them — this is what phi nodes would do in
  traditional SSA.

- **`br_if v2, block_then(v0), block_else(v0)`** — conditional branch
  with arguments to both targets. If v2 is true, jump to `block_then`
  passing v0. Otherwise fall through to `block_else` passing v0.

### What's live at each safepoint

Each `fuel_check` is labeled `[sN]` with its live vregs — the values that
must be preserved if we suspend here.

**`$double_if_small`:**
```
  [s0] after iconst 3:       live: v0 (x), v1 (3)           — 2 × i32
  [s1] after le_s:           live: v0 (x), v2 (cmp result)  — 2 × i32
  [s2] in block_then:        live: v4 (x+x)                 — 1 × i32
  [s3] in block_else:        live: v6 (x)                   — 1 × i32
```

**`$sum_doubled`:**
```
  [s0] after iconst 0:       live: v0 (n), v1 (0)                 — 2 × i32
  [s1] after iconst 0:       live: v2 (i), v3 (acc), v4 (0)       — 3 × i32
  [s2] after le_s:           live: v2 (i), v3 (acc), v5 (cmp)     — 3 × i32
  [s3] after call:           live: v2 (i), v3 (acc), v6 (result)  — 3 × i32
  [s4] after add:            live: v2 (i), v7 (new_acc)           — 2 × i32
  [s5] after iconst 1:       live: v2 (i), v7 (new_acc), v8 (1)  — 3 × i32
  [s6] after sub:            live: v7 (new_acc), v9 (new_i)       — 2 × i32
```

**Max live at any single safepoint: 3 × i32.**

**Suspend inside `$double_if_small` called from `$sum_doubled`:**
```
  $sum_doubled frame:         v2 (i), v3 (acc)  — caller state before call
  $double_if_small frame:     v0 (x)            — at whichever safepoint
  native call stack:          [sum_doubled ret addr] → [double_if_small]
  total preserved state:      3 × i32 + return addresses
```

---

## 4. Recursive fib example

This matches the actual fib from `bench_fib.rs` — uses locals `$a`/`$b`
and early return, not if/else with result.

### Rust-ish pseudocode

```rust
fn fib(n: i32) -> i32 {
    if n <= 1 {
        return n;
    }
    let a = fib(n - 1);
    let b = fib(n - 2);
    a + b
}
```

### Trace: `fib(4)`

```
fib(4)
  4 > 1 → continue
    a = fib(3)
      3 > 1 → continue
        a = fib(2)
          2 > 1 → continue
            a = fib(1) = 1    (base case: return n)
            b = fib(0) = 0    (base case: return n)
            return 1 + 0 = 1
        b = fib(1) = 1        (base case: return n)
        return 1 + 1 = 2
    b = fib(2)
      2 > 1 → continue
        a = fib(1) = 1
        b = fib(0) = 0
        return 1
    return 2 + 1 = 3
→ fib(4) = 3
```

### WAT

```wat
(module
  (func $fib (export "fib") (param $n i32) (result i32)
    (local $a i32)
    (local $b i32)
    (if (i32.le_s (local.get $n) (i32.const 1))
      (then (return (local.get $n)))
    )
    (local.set $a (call $fib (i32.sub (local.get $n) (i32.const 1))))
    (local.set $b (call $fib (i32.sub (local.get $n) (i32.const 2))))
    (i32.add (local.get $a) (local.get $b))
  )
)
```

Note: this `if` has no `else` and no result type. The `then` branch
does an early `return`. If the condition is false, execution falls
through past the `if`/`end` and continues with the recursive calls.
Locals `$a` and `$b` are used to hold call results across the two calls.

### Block-argument SSA IR

The `if` with early return compiles to a conditional branch to a
return block. No merge needed — the "else" is just the rest of the
function body (fall-through).

Locals `$n`, `$a`, `$b` are at frame slots 0, 1, 2.

```asm
func $fib(v0: i32) -> i32:
    ;; frame: [slot0: $n] [slot1: $a] [slot2: $b]

    block_entry(v0: i32):                        ;; v0 = n
        local.set slot0, v0                       ;; $n = v0 (param → frame)

        ;; if (i32.le_s (local.get $n) (i32.const 1))
        v1 = local.get slot0                      ;; $n
        suspend_check suspend_s0(v1)
        v2 = iconst 1
        suspend_check suspend_s1(v1, v2)
        v3 = i32.le_s v1, v2                      ;; n <= 1?
        suspend_check suspend_s2(v3)
        br_if v3, block_base(), block_body()

    block_base():                                 ;; single pred: inlineable
        ;; (then (return (local.get $n)))
        v4 = local.get slot0                      ;; $n
        suspend_check suspend_s3(v4)
        return v4

    block_body():                                 ;; single pred: inlineable
        ;; (local.set $a (call $fib (i32.sub (local.get $n) (i32.const 1))))
        v5 = local.get slot0                      ;; $n
        suspend_check suspend_s4(v5)
        v6 = iconst 1
        suspend_check suspend_s5(v5, v6)
        v7 = i32.sub v5, v6                       ;; n - 1
        suspend_check suspend_s6(v7)
        v8 = call $fib(v7)                         ;; a = fib(n-1)
        suspend_check suspend_s7(v8)
        local.set slot1, v8                        ;; $a = v8

        ;; (local.set $b (call $fib (i32.sub (local.get $n) (i32.const 2))))
        v9 = local.get slot0                       ;; $n
        suspend_check suspend_s8(v9)
        v10 = iconst 2
        suspend_check suspend_s9(v9, v10)
        v11 = i32.sub v9, v10                      ;; n - 2
        suspend_check suspend_s10(v11)
        v12 = call $fib(v11)                        ;; b = fib(n-2)
        suspend_check suspend_s11(v12)
        local.set slot2, v12                        ;; $b = v12

        ;; (i32.add (local.get $a) (local.get $b))
        v13 = local.get slot1                       ;; $a
        suspend_check suspend_s12(v13)
        v14 = local.get slot2                       ;; $b
        suspend_check suspend_s13(v13, v14)
        v15 = i32.add v13, v14                      ;; a + b
        suspend_check suspend_s14(v15)
        return v15

    ;; --- suspend stubs ---
    suspend_s0(v1: i32):                          todo
    suspend_s1(v1: i32, v2: i32):                todo
    suspend_s2(v3: i32):                          todo
    suspend_s3(v4: i32):                          todo
    suspend_s4(v5: i32):                          todo
    suspend_s5(v5: i32, v6: i32):                todo
    suspend_s6(v7: i32):                          todo  ;; about to call fib(n-1)
    suspend_s7(v8: i32):                          todo  ;; a = fib(n-1) done, about to store
    suspend_s8(v9: i32):                          todo
    suspend_s9(v9: i32, v10: i32):               todo
    suspend_s10(v11: i32):                        todo  ;; about to call fib(n-2)
    suspend_s11(v12: i32):                        todo  ;; b = fib(n-2) done, about to store
    suspend_s12(v13: i32):                        todo
    suspend_s13(v13: i32, v14: i32):             todo
    suspend_s14(v15: i32):                        todo
```

### Key difference from the previous examples

**Locals act as the frame.** Instead of threading values through block
arguments, this version uses `local.set`/`local.get` to spill values
to frame slots. The call result `v8` is stored to `slot1` ($a) before
the second call begins. On resume, `$a` is reloaded from the frame.

This means the suspend stubs don't need to carry `$a` in their argument
list across the second call — it's already in the frame. The live vreg
set at each suspend point is small because locals absorb the cross-call
state.

**Suspend at depth with locals-based frames:**

```
fib(4) frame: [slot0=4, slot1=?, slot2=?]   suspended at s6, about to call fib(3)
fib(3) frame: [slot0=3, slot1=?, slot2=?]   suspended at s6, about to call fib(2)
fib(2) frame: [slot0=2, slot1=1,  slot2=?]  suspended at s10, a=1, about to call fib(0)
← suspended here
```

Each frame is 3 × i32 (the three locals). `slot1`/`slot2` are only
meaningful after their respective calls complete — but the frame
*always* has 3 slots allocated.

### Why this version matters

This is what our compiler actually emits today. The previous
`if/else`-with-result style is more "SSA-pure" but our wasm frontend
produces the locals-based version. The suspend stubs work either way —
but here, the frame slots do most of the heavy lifting for preserving
state across calls, and the suspend stub args are just the in-flight
vregs that haven't been stored yet.

### Fused block-argument SSA IR

Our frontend fuses common wasm op sequences into superinstructions
before IR generation. Each fused op is like an inline function call —
it takes typed inputs (locals, constants) and returns results in vregs.
Constants fold directly into the fused op (no separate `iconst` vreg).

Fusions that fire for fib:

| Fused op | Replaces |
|---|---|
| `LocalGetI32ConstLeSIf(slot, k, block)` | `local.get` + `i32.const` + `i32.le_s` + `if` |
| `LocalGetI32ConstSub(slot, k)` → vreg | `local.get` + `i32.const` + `i32.sub` |
| `CallLocalSet(func, slot, args...)` | `call` + `local.set` |
| `LocalGetLocalGetAdd(slotA, slotB)` → vreg | `local.get` + `local.get` + `i32.add` |
| `LocalGetReturn(slot)` | `local.get` + `return` |

#### Vreg naming convention

- `vl0_n` — vreg bound to local 0 (`$n`), loaded from frame
- `v1`, `v2`... — transient vregs (intermediate results, not stored)

#### Local initialization

Wasm requires declared locals to be zero-initialized. Params get
their value from the caller. The prologue makes this explicit:

- **Params** (slot0 `$n`): bound from function argument
- **Declared locals** (slot1 `$a`, slot2 `$b`): zero-initialized

In practice, our frame memory comes from `JitContext` which is
`mem::zeroed()`, so the zeroing is "free" for the first entry. But
the prologue must still be explicit in the IR because on a *recursive*
call, the callee gets a fresh frame region — and those slots must be
zeroed, not leftover garbage from a previous activation.

#### Canonicalization

A frame is **canonical** when all live state is in frame slots — no
values trapped in registers. The suspend stubs exist precisely to
canonicalize: they take in-flight vregs and write them to frame slots
before yielding. On resume, the frame is self-describing.

The rule: **always stash, never recompute.** Fused ops are opaque — we
can't assume any computation is cheap or side-effect-free. Every
in-flight vreg gets written to a scratch slot in the frame.

```
canonical frame for $fib (fp = x29, pointing to base of this frame):
  fp+0x00  [slot0: $n  (i32)]       local 0 (param)
  fp+0x08  [slot1: $a  (i32)]       local 1 (declared, zero-init)
  fp+0x10  [slot2: $b  (i32)]       local 2 (declared, zero-init)
  fp+0x18  [scratch0   (i32)]       in-flight vreg (max 1 for fib fused)
  fp+0x20  [suspend_id (u32)]       which instruction to resume at
```
Frame size: 5 × 8 = 40 bytes (all slots 8-byte aligned for simplicity).

- **Locals** (fp+0x00–0x10): always present, always up to date.
- **Scratch** (fp+0x18): holds the one in-flight vreg (if any) that
  hasn't been stored to a local yet. Count = max live vregs at any
  suspend point (fib fused: 1).
- **suspend_id** (fp+0x20): which instruction to resume at.

Together, this is the complete state needed to continue execution.

#### Lowered to aarch64 registers

To see what actually gets spilled, let's drop to real registers.

Our ABI:
- **x9–x15**: scratch regs (vregs map here). Caller-saved — clobbered by calls.
- **x29 (fp)**: frame pointer. Points to base of current locals frame.
- **x21**: fuel counter.
- **x20**: context pointer.
- **x30 (lr)**: return address.
- **Args passed in x9–x15**, result returned in x9.

```asm
$fib:
    ;; frame layout:
    ;;   [fp+0x00] $n    (local 0, param)
    ;;   [fp+0x08] $a    (local 1, declared)
    ;;   [fp+0x10] $b    (local 2, declared)
    ;;   [fp+0x18] scratch0
    ;;   [fp+0x20] suspend_id
    ;; frame size = 0x28 (40 bytes)

    ;; === prologue ===
    ;; x9 = param $n (from caller)
    str x9, [x29, #0x00]           ;; stack[fp+0x00] = $n  (spill param to frame)
    ;; NOTE: x9 still holds $n! We can keep using it.
    ;; $a, $b: not zeroed (Option D — cold-path zeroing)

    ;; === LocalGetI32ConstLeSIf(slot0, 1) ===
    ;; x9 already has $n from the param — no reload needed.
    cmp w9, #1                      ;; n <= 1?
    ;; fuel check (suspend_s0)
    subs x21, x21, #1              ;; fuel--
    b.le suspend_s0                ;; if fuel exhausted, go to suspend stub
    ;; branch
    b.le .base_case                ;; if n <= 1, jump to base case
    ;; fall through to body

    ;; === block_body ===

    ;; === LocalGetI32ConstSub(slot0, 1) → x10 ===
    ;; x9 still has $n (no call has clobbered it yet)
    sub w10, w9, #1                 ;; x10 = n - 1
    ;; fuel check (suspend_s1)
    subs x21, x21, #1
    b.le suspend_s1                ;; x10 is live (n-1)

    ;; === CallLocalSet($fib, slot1, x10) ===
    ;; Prepare call: arg goes in x9
    mov x9, x10                     ;; x9 = n-1 (arg for callee)
    ;; Save lr, advance fp for callee's frame
    stp x29, x30, [sp, #-16]!      ;; push caller's fp + lr
    add x29, x29, #0x28            ;; fp += frame_size (callee gets fresh frame)
    bl $fib                         ;; CALL — clobbers x9-x15!
    ;; Return: result in x9
    ldp x29, x30, [sp], #16        ;; restore caller's fp + lr
    str x9, [x29, #0x08]           ;; stack[fp+0x08] = result ($a = fib(n-1))
    ;; fuel check (suspend_s2)
    subs x21, x21, #1
    b.le suspend_s2                ;; no live scratch regs — $a is in frame

    ;; === LocalGetI32ConstSub(slot0, 2) → x10 ===
    ;; x9 was CLOBBERED by the call! Must reload $n from frame.
    ldr x9, [x29, #0x00]           ;; x9 = stack[fp+0x00] ($n)  ← THIS is the reload
    sub w10, w9, #2                 ;; x10 = n - 2
    ;; fuel check (suspend_s3)
    subs x21, x21, #1
    b.le suspend_s3                ;; x10 is live (n-2)

    ;; === CallLocalSet($fib, slot2, x10) ===
    mov x9, x10                     ;; x9 = n-2 (arg for callee)
    stp x29, x30, [sp, #-16]!
    add x29, x29, #0x28
    bl $fib                         ;; CALL — clobbers x9-x15!
    ldp x29, x30, [sp], #16
    str x9, [x29, #0x10]           ;; stack[fp+0x10] = result ($b = fib(n-2))
    ;; fuel check (suspend_s4)
    subs x21, x21, #1
    b.le suspend_s4                ;; no live scratch regs

    ;; === LocalGetLocalGetAdd(slot1, slot2) → x9 ===
    ldr x9, [x29, #0x08]           ;; x9 = $a
    ldr x10, [x29, #0x10]          ;; x10 = $b
    add w9, w9, w10                 ;; x9 = a + b
    ;; fuel check (suspend_s5)
    subs x21, x21, #1
    b.le suspend_s5                ;; x9 is live (result)
    ret                             ;; return x9

.base_case:
    ;; x9 still has $n (or reload: ldr x9, [x29, #0x00])
    ;; fuel check (suspend_s3... actually this is a separate path)
    ret                             ;; return x9 (= n)

    ;; === suspend stubs (cold path) ===

suspend_s0:                         ;; cmp result in NZCV, x9 = $n
    ;; the cmp result is in the flags, not a vreg.
    ;; we need to re-derive it on resume. But we said no recompute...
    ;; actually: we can stash x9 ($n) and recompute the cmp on resume.
    ;; OR: materialize the flag to a register and stash that.
    cset w10, le                    ;; w10 = (n <= 1) ? 1 : 0
    str x10, [x29, #0x18]          ;; stack[fp+0x18] = cmp result
    ;; zero unassigned locals (Option D)
    str xzr, [x29, #0x08]          ;; $a = 0
    str xzr, [x29, #0x10]          ;; $b = 0
    mov w10, #0
    str x10, [x29, #0x20]          ;; suspend_id = 0
    yield

suspend_s1:                         ;; x10 = n-1
    str x10, [x29, #0x18]          ;; stack[fp+0x18] = n-1
    str xzr, [x29, #0x08]          ;; $a = 0 (unassigned)
    str xzr, [x29, #0x10]          ;; $b = 0 (unassigned)
    mov w10, #1
    str x10, [x29, #0x20]          ;; suspend_id = 1
    yield

suspend_s2:                         ;; no live scratch regs
    str xzr, [x29, #0x10]          ;; $b = 0 (unassigned, $a already stored)
    mov w10, #2
    str x10, [x29, #0x20]          ;; suspend_id = 2
    yield

suspend_s3:                         ;; x10 = n-2
    str x10, [x29, #0x18]          ;; stack[fp+0x18] = n-2
    str xzr, [x29, #0x10]          ;; $b = 0 (unassigned, $a stored)
    mov w10, #3
    str x10, [x29, #0x20]          ;; suspend_id = 3
    yield

suspend_s4:                         ;; no live scratch regs
    mov w10, #4
    str x10, [x29, #0x20]          ;; suspend_id = 4
    yield                           ;; $a and $b both in frame

suspend_s5:                         ;; x9 = a+b (result)
    str x9, [x29, #0x18]           ;; stack[fp+0x18] = result
    mov w10, #5
    str x10, [x29, #0x20]          ;; suspend_id = 5
    yield
```

#### What this reveals

**1. The first use of `$n` does NOT reload from the stack.**
After `str x9, [x29, #0x00]` in the prologue, x9 still holds `$n`.
The `cmp w9, #1` and `sub w10, w9, #1` use it directly from the
register. No unnecessary load.

**2. The reload happens after the first call — and it's unavoidable.**
`bl $fib` clobbers x9. So `ldr x9, [x29, #0x00]` before the second
`sub` is a real, necessary reload. The store in the prologue exists
precisely for this moment.

**3. After `CallLocalSet`, there are zero live scratch regs.**
The call result goes straight from x9 to `str x9, [x29, #0x08]`.
At `suspend_s2` and `suspend_s4`, there's nothing in flight to save.

**4. The prologue store of `$n` is the only hot-path store that "matters".**
With Option D (cold-path zeroing), the prologue is just one store:
`str x9, [x29, #0x00]`. The `$a`/`$b` zeroing moves to the suspend
stubs. The hot path for the base case (n ≤ 1) is:

```asm
    str x9, [x29, #0x00]       ;; store $n
    cmp w9, #1
    subs x21, x21, #1          ;; fuel check
    b.le suspend_s0
    b.le .base_case
    ...
.base_case:
    ret                         ;; return x9 (= n)
```

That's 5 instructions for the base case. The zeroing of `$a`/`$b`
only happens in the suspend stubs (cold path).

```asm
func $fib(vl0_n: i32) -> i32:
    ;; frame layout:
    ;;   fp+0x00: $n         (local 0, param)
    ;;   fp+0x08: $a         (local 1, declared)
    ;;   fp+0x10: $b         (local 2, declared)
    ;;   fp+0x18: scratch0   (in-flight vreg spill)
    ;;   fp+0x20: suspend_id
    ;;
    ;; prologue: bind param, zero-init declared locals

    block_entry(vl0_n: i32):
        stack[fp+0x00] = vl0_n                    ;; $n = param 0
        stack[fp+0x08] = 0i32                     ;; $a = 0 (zero-init)
        stack[fp+0x10] = 0i32                     ;; $b = 0 (zero-init)

        ;; fused: local.get $n + i32.const 1 + i32.le_s + if
        ;;   internally: v_n = stack[fp+0x00]; v1 = (v_n <= 1)
        v1 = LocalGetI32ConstLeSIf(slot0, 1)
        suspend_check suspend_s0(v1)
        br_if v1, block_base(), block_body()

    block_base():                                 ;; single pred: inlineable
        ;; fused: local.get $n + return
        ;;   internally: v_ret = stack[fp+0x00]; return v_ret
        LocalGetReturn(slot0)

    block_body():                                 ;; single pred: inlineable
        ;; fused: local.get $n + i32.const 1 + i32.sub
        ;;   internally: v_n = stack[fp+0x00]; v2 = v_n - 1
        v2 = LocalGetI32ConstSub(slot0, 1)       ;; v2 = n - 1 (in register)
        suspend_check suspend_s1(v2)

        ;; fused: call $fib(v2) + local.set $a
        ;;   internally: v_ret = call $fib(v2); stack[fp+0x08] = v_ret
        ;;   v2 is consumed as the call arg. $n survives in stack[fp+0x00].
        ;;   after return, result goes directly to stack[fp+0x08] ($a).
        CallLocalSet($fib, slot1, v2)
        suspend_check suspend_s2()                ;; no live vregs — $a in frame

        ;; fused: local.get $n + i32.const 2 + i32.sub
        ;;   internally: v_n = stack[fp+0x00]; v3 = v_n - 2
        ;;   $n reloaded from frame (survived the call in stack[fp+0x00])
        v3 = LocalGetI32ConstSub(slot0, 2)       ;; v3 = n - 2 (in register)
        suspend_check suspend_s3(v3)

        ;; fused: call $fib(v3) + local.set $b
        ;;   internally: v_ret = call $fib(v3); stack[fp+0x10] = v_ret
        CallLocalSet($fib, slot2, v3)
        suspend_check suspend_s4()                ;; no live vregs — $b in frame

        ;; fused: local.get $a + local.get $b + i32.add
        ;;   internally: v_a = stack[fp+0x08]; v_b = stack[fp+0x10]; v4 = v_a + v_b
        v4 = LocalGetLocalGetAdd(slot1, slot2)    ;; v4 = a + b (in register)
        suspend_check suspend_s5(v4)
        return v4

    ;; --- suspend stubs (canonicalize + yield) ---
    ;;
    ;; Each stub writes ALL in-flight vregs to scratch slots,
    ;; records suspend_id, and yields. Fused ops are opaque — always stash.

    suspend_s0(v1: i32):                          ;; after condition check
        stack[fp+0x18] = v1                       ;; scratch0 = cmp result
        stack[fp+0x20] = 0u32                     ;; suspend_id = 0
        yield

    suspend_s1(v2: i32):                          ;; have n-1, about to call
        stack[fp+0x18] = v2                       ;; scratch0 = n-1
        stack[fp+0x20] = 1u32                     ;; suspend_id = 1
        yield

    suspend_s2():                                 ;; $a in frame, about to compute n-2
        stack[fp+0x20] = 2u32                     ;; suspend_id = 2
        yield                                     ;; nothing to stash

    suspend_s3(v3: i32):                          ;; have n-2, about to call
        stack[fp+0x18] = v3                       ;; scratch0 = n-2
        stack[fp+0x20] = 3u32                     ;; suspend_id = 3
        yield

    suspend_s4():                                 ;; $b in frame, about to add
        stack[fp+0x20] = 4u32                     ;; suspend_id = 4
        yield                                     ;; nothing to stash

    suspend_s5(v4: i32):                          ;; have a+b, about to return
        stack[fp+0x18] = v4                       ;; scratch0 = a+b
        stack[fp+0x20] = 5u32                     ;; suspend_id = 5
        yield
```

**Unfused: 15 suspend points, max 2 live vregs per stub.**
**Fused: 6 suspend points, max 1 live vreg per stub.**

Fusing collapses multiple primitive ops into single "macro" instructions.
Each fused op does its own local.get/const internally, so those intermediate
vregs never appear in the IR — they don't need suspend stubs.

`CallLocalSet` is especially powerful: the call result goes directly to
a frame slot, so `suspend_s2()` and `suspend_s4()` have **zero live vregs**.
The frame is already canonical — nothing to stash.

#### Resume dispatch

On resume, the runtime reads `suspend_id` from the frame and jumps to
the corresponding resume point. Each resume point reloads its scratch
slots from concrete offsets and continues:

```asm
resume(fp):
    v_sid = stack[fp+0x20]                        ;; read suspend_id
    match v_sid:
        0 → v1 = stack[fp+0x18]; goto after_s0
        1 → v2 = stack[fp+0x18]; goto after_s1
        2 → goto after_s2
        3 → v3 = stack[fp+0x18]; goto after_s3
        4 → goto after_s4
        5 → v4 = stack[fp+0x18]; goto after_s5
```

---

## 5. Prologue zeroing: design variations

### The problem

Wasm requires declared locals to be zero-initialized. In the IR above,
the prologue does `stack_store(fp+0x08, 0)` and `stack_store(fp+0x10, 0)`
for `$a` and `$b`. This is wasted work on the hot path — fib(30) makes
~2.7M calls, each paying 2 stores for locals that get overwritten later.

But the canonical frame must have valid values in all slots for
suspend/serialize to work. An interpreter consuming a serialized frame
expects `$a` and `$b` to be zero if they haven't been assigned yet.

### Option A: Always zero in prologue

```asm
block_entry(vl0_n: i32):
    stack[fp+0x00] = vl0_n                    ;; $n = param
    stack[fp+0x08] = 0i32                     ;; $a = 0       ← hot path cost
    stack[fp+0x10] = 0i32                     ;; $b = 0       ← hot path cost
    ...
```

- **Hot path**: 2 extra stores per call. Simple, always correct.
- **Suspend**: trivial — frame is already canonical at all times.
- **Cost for fib(30)**: ~5.4M unnecessary stores.

### Option B: Suspend cascade (return, don't yield)

Instead of yielding directly, the deepest frame that exhausts fuel
*returns* to its caller with a "suspended" signal. The caller's next
`suspend_check` sees fuel is still ≤ 0 and enters its own suspend stub.
This cascades up the call stack, each frame canonicalizing on the way out.

```asm
block_entry(vl0_n: i32):
    stack[fp+0x00] = vl0_n                    ;; $n = param
    ;; NO zeroing of $a, $b
    ...

suspend_s1(v2: i32):                         ;; have n-1, about to call
    stack[fp+0x08] = 0i32                     ;; $a = 0 (unassigned at this point)
    stack[fp+0x10] = 0i32                     ;; $b = 0 (unassigned at this point)
    stack[fp+0x18] = v2                       ;; scratch0 = n-1
    stack[fp+0x20] = 1u32                     ;; suspend_id = 1
    return SUSPENDED                          ;; ← return, not yield

;; Caller receives SUSPENDED, hits its own suspend_check,
;; enters its own suspend stub, canonicalizes its own frame, returns...
;; ...cascades all the way up to the fiber entry point.
```

- **Hot path**: zero overhead for local zeroing.
- **Suspend**: each frame canonicalizes itself during the cascade.
  The stub knows statically which locals are unassigned and writes
  explicit zeros for them.
- **Tradeoff**: suspend is slower (N returns instead of 1 yield),
  but suspend is the cold path — we don't care.
- **Problem**: the cascade requires each caller to check the return
  value of every call, which adds branching to the hot path. Unless
  we use the fuel register itself as the signal (fuel ≤ 0 means
  "something below me suspended, check yourself").

### Option C: Zero registers, not memory

```asm
block_entry(vl0_n: i32):
    stack[fp+0x00] = vl0_n                    ;; $n = param
    v_a = 0i32                                ;; $a = 0 in register (1 cycle, no memory)
    v_b = 0i32                                ;; $b = 0 in register (1 cycle, no memory)
    ...
```

- **Hot path**: 2 register moves (~1 cycle each) instead of 2 stores.
- **Suspend**: stubs write register values to frame slots. If `$a`
  is still in a register holding 0, the store writes 0 correctly.
- **Cost**: minimal. Register zeroing is essentially free on modern
  CPUs (zero-idiom elimination).
- **Limitation**: only works if locals live in registers, not if they
  spill to memory between operations. With our current register
  allocator (vregs → scratch regs x9-x15), we have 7 regs for locals
  + scratch. For fib (3 locals + some scratch), this works fine.

### Option D: Suspend stubs zero unassigned locals (cold-path only)

```asm
block_entry(vl0_n: i32):
    stack[fp+0x00] = vl0_n                    ;; $n = param
    ;; NO zeroing — frame slots for $a, $b contain garbage
    ...
```

The compiler statically knows at each suspend point which locals
have been assigned (via `local.set` or `CallLocalSet`). The suspend
stub writes zeros for unassigned locals:

```asm
suspend_s0(v1: i32):                         ;; $a: unassigned, $b: unassigned
    stack[fp+0x08] = 0i32                     ;; $a = 0
    stack[fp+0x10] = 0i32                     ;; $b = 0
    stack[fp+0x18] = v1                       ;; scratch0
    stack[fp+0x20] = 0u32                     ;; suspend_id = 0
    yield

suspend_s1(v2: i32):                         ;; $a: unassigned, $b: unassigned
    stack[fp+0x08] = 0i32                     ;; $a = 0
    stack[fp+0x10] = 0i32                     ;; $b = 0
    stack[fp+0x18] = v2                       ;; scratch0
    stack[fp+0x20] = 1u32                     ;; suspend_id = 1
    yield

suspend_s2():                                ;; $a: ASSIGNED (by CallLocalSet), $b: unassigned
    stack[fp+0x10] = 0i32                     ;; $b = 0 (only $b needs zeroing)
    stack[fp+0x20] = 2u32                     ;; suspend_id = 2
    yield

suspend_s3(v3: i32):                         ;; $a: assigned, $b: unassigned
    stack[fp+0x10] = 0i32                     ;; $b = 0
    stack[fp+0x18] = v3                       ;; scratch0
    stack[fp+0x20] = 3u32                     ;; suspend_id = 3
    yield

suspend_s4():                                ;; $a: assigned, $b: ASSIGNED
    stack[fp+0x20] = 4u32                     ;; suspend_id = 4
    yield                                     ;; both locals already in frame

suspend_s5(v4: i32):                         ;; $a: assigned, $b: assigned
    stack[fp+0x18] = v4                       ;; scratch0
    stack[fp+0x20] = 5u32                     ;; suspend_id = 5
    yield
```

- **Hot path**: zero overhead. No stores, no reg zeroing.
- **Suspend**: stubs are slightly larger (extra zero-stores for
  unassigned locals), but this is cold path code.
- **Correctness**: the compiler tracks assignment status at each
  suspend point at compile time. This is a simple forward dataflow:
  a local is "assigned" after any `local.set` / `CallLocalSet` to it.
- **Code size**: stubs grow by 1 store per unassigned local. For fib,
  early stubs have +2 stores, later stubs have +1 or +0.

### Comparison

| Variation | Hot path cost | Suspend cost | Complexity |
|---|---|---|---|
| A: always zero | 2 stores/call | minimal | trivial |
| B: cascade | 0 | N returns up stack | moderate (fuel-as-signal) |
| C: zero regs | 2 reg movs/call | write regs to frame | low |
| D: cold-path zero | 0 | bigger stubs | low (static dataflow) |

**Option D is the clear winner**: zero hot-path cost, the suspend
stubs do the extra work, and the compiler already knows which locals
are assigned at each point. Options B and D can also be combined —
cascade return + cold-path zeroing — to avoid the direct yield.

---

## 6. Nested-block IR syntax

The SSA IR in sections 3–4 uses flat blocks with jump labels. That's
fine for a compiler, but hard to read — you have to mentally trace
branches across labels. This section defines a nested-block syntax
where execution reads top-to-bottom, branches are indented inline,
and suspend/resume blocks appear right where they happen.

### Design principles

1. **Chronological flow.** You read the IR like the program runs.
   No forward jumps to labels. Branches are nested blocks.
   Suspend/resume appear inline at the point they're relevant.

2. **Three block kinds, all inline:**
   - **Control flow blocks** (`br.if`, `loop`): hot-path branching,
     nested where they execute.
   - **`suspend:N { ... }`**: cold-path canonicalization stub.
     Appears right after the `fuel_check` it guards. You see
     "what would happen if we ran out of fuel *here*" in context.
   - **`resume:N { ... }`**: metadata recipe for reconstructing
     vregs from the canonical frame. Appears right after its
     matching `suspend:N`. You see "how to come back to *this*
     point" without scrolling.

3. **`consume:` prefix.** Marks the last use of a vreg. The register
   is freed after this instruction. Example: `call $fib(consume: v2)`
   means v2 is passed to the call and never used again.

4. **Pinned globals.** `g.fuel`, `g.fp`, `g.ctx` are always live.
   They are not vregs — they're pinned to physical registers and
   never consumed.

5. **Frame access.** `stack[g.fp + 0xNN]` for explicit loads/stores.
   No implicit spills.

### Notation summary

```
func $name(params...) -> rettype {
    v1 = i32.const 42
    v2 = i32.add(v0, consume: v1)

    // fuel check — suspend/resume appear right here
    fuel_check
    suspend:0 {
        // canonicalize frame + return SUSPENDED
    }
    resume:0 {
        // recipe to reconstruct vregs from canonical frame
        // continue at: next instruction
    }

    // conditional branch (nested)
    br.if (consume: v2) {
        ret v0
    }
    // fall-through continues here

    // loop with block-argument bindings
    loop (v3 = v_init, v4 = 0i32) {
        fuel_check
        suspend:1 { ... }
        resume:1 { ... }

        br.if (consume: v_cond) {
            break v_result
        }
        continue (v3_next, v4_next)
    } -> v_out
    ret v_out
}
```

### Fib in nested-block IR

Using Option D (cold-path zeroing) and fused ops:

```
func $fib(v0_n: i32) -> i32 {
    // frame: [0x00: $n] [0x08: $a] [0x10: $b] [0x18: scratch0] [0x20: suspend_id]

    // prologue: bind param (no zeroing — Option D)
    stack[g.fp + 0x00] = v0_n

    // fused: local.get $n + i32.const 1 + i32.le_s
    v1 = LocalGetI32ConstLeS(slot0, 1)          // v1 = ($n <= 1)

    fuel_check
    suspend:0 {
        // v1 = cmp result is in flight. $a, $b unassigned → zero.
        stack[g.fp + 0x08] = 0i32               // $a = 0
        stack[g.fp + 0x10] = 0i32               // $b = 0
        stack[g.fp + 0x18] = v1                 // scratch0 = cmp result
        stack[g.fp + 0x20] = 0u32               // suspend_id = 0
        ret SUSPENDED
    }
    resume:0 {
        v1 = stack[g.fp + 0x18]                 // scratch0 → cmp result
        // continue at: br.if (v1)
    }

    br.if (consume: v1) {
        // base case: return $n
        v_ret = local.get slot0
        ret v_ret
    }

    // --- recursive case (fall-through) ---

    // fused: local.get $n + i32.const 1 + i32.sub
    v2 = LocalGetI32ConstSub(slot0, 1)          // v2 = n - 1

    fuel_check
    suspend:1 {
        // v2 = n-1 in flight. $a, $b unassigned.
        stack[g.fp + 0x08] = 0i32               // $a = 0
        stack[g.fp + 0x10] = 0i32               // $b = 0
        stack[g.fp + 0x18] = v2                 // scratch0 = n-1
        stack[g.fp + 0x20] = 1u32               // suspend_id = 1
        ret SUSPENDED
    }
    resume:1 {
        v2 = stack[g.fp + 0x18]                 // scratch0 → n-1
        // continue at: CallLocalSet($fib, slot1, v2)
    }

    // fused: call $fib(v2) + local.set $a
    // v2 consumed as call arg. result → stack[g.fp + 0x08].
    CallLocalSet($fib, slot1, consume: v2)

    fuel_check
    suspend:2 {
        // no live vregs — $a already in frame. $b unassigned.
        stack[g.fp + 0x10] = 0i32               // $b = 0
        stack[g.fp + 0x20] = 2u32               // suspend_id = 2
        ret SUSPENDED
    }
    resume:2 {
        // no scratch to reload. $a in frame.
        // continue at: LocalGetI32ConstSub(slot0, 2)
    }

    // fused: local.get $n + i32.const 2 + i32.sub
    // $n reloaded from frame (clobbered by call)
    v3 = LocalGetI32ConstSub(slot0, 2)          // v3 = n - 2

    fuel_check
    suspend:3 {
        // v3 = n-2 in flight. $a assigned, $b unassigned.
        stack[g.fp + 0x10] = 0i32               // $b = 0
        stack[g.fp + 0x18] = v3                 // scratch0 = n-2
        stack[g.fp + 0x20] = 3u32               // suspend_id = 3
        ret SUSPENDED
    }
    resume:3 {
        v3 = stack[g.fp + 0x18]                 // scratch0 → n-2
        // continue at: CallLocalSet($fib, slot2, v3)
    }

    // fused: call $fib(v3) + local.set $b
    CallLocalSet($fib, slot2, consume: v3)

    fuel_check
    suspend:4 {
        // no live vregs — $a, $b both in frame.
        stack[g.fp + 0x20] = 4u32               // suspend_id = 4
        ret SUSPENDED
    }
    resume:4 {
        // no scratch to reload. $a, $b in frame.
        // continue at: LocalGetLocalGetAdd(slot1, slot2)
    }

    // fused: local.get $a + local.get $b + i32.add
    v4 = LocalGetLocalGetAdd(slot1, slot2)      // v4 = a + b

    fuel_check
    suspend:5 {
        // v4 = a+b in flight. $a, $b assigned.
        stack[g.fp + 0x18] = v4                 // scratch0 = a+b
        stack[g.fp + 0x20] = 5u32               // suspend_id = 5
        ret SUSPENDED
    }
    resume:5 {
        v4 = stack[g.fp + 0x18]                 // scratch0 → a+b
        // continue at: ret v4
    }

    ret consume: v4
}
```

### Reading this

At every `fuel_check`, you see three things in sequence:

1. **The hot path** — just falls through (fuel > 0). Two
   instructions in machine code: `subs + b.le`.

2. **`suspend:N { ... }`** — "if fuel ran out *right here*, what
   happens?" Canonicalize the frame, return SUSPENDED. You see
   exactly which vregs are in flight and which locals need zeroing,
   *in the context where it matters*.

3. **`resume:N { ... }`** — "if the runtime needs to restart *right
   here*, how does it reconstruct vregs?" Load scratch slots, then
   continue at the next instruction. The resume recipe sits right
   next to the suspend it undoes.

**`consume:`** — marks the last use of a vreg. After
`call $fib(consume: v2)`, v2 is dead and its register is free.

**`br.if (consume: v1) { ... }`** — the taken path is indented
inline. Fall-through continues after the closing brace.

### sum_doubled in nested-block IR

```
func $sum_doubled(v0_n: i32) -> i32 {
    // frame: [0x00: $n] [0x08: $i] [0x10: $acc] [0x18: scratch0] [0x20: suspend_id]

    // prologue
    stack[g.fp + 0x00] = v0_n

    v_i = v0_n
    v_acc = i32.const 0

    loop (v_i, v_acc) {
        v_done = i32.le_s(v_i, 0)

        fuel_check
        suspend:0 {
            stack[g.fp + 0x08] = v_i
            stack[g.fp + 0x10] = v_acc
            stack[g.fp + 0x20] = 0u32
            ret SUSPENDED
        }
        resume:0 {
            v_i = stack[g.fp + 0x08]
            v_acc = stack[g.fp + 0x10]
            // continue at: br.if (v_done)
        }

        br.if (consume: v_done) {
            break v_acc
        }

        // spill before call (scratch regs clobbered)
        stack[g.fp + 0x08] = v_i
        stack[g.fp + 0x10] = v_acc
        v_result = call $double_if_small(v_i)

        fuel_check
        suspend:1 {
            // $i, $acc already in frame. v_result in scratch.
            stack[g.fp + 0x18] = v_result
            stack[g.fp + 0x20] = 1u32
            ret SUSPENDED
        }
        resume:1 {
            v_result = stack[g.fp + 0x18]
            // $i, $acc reloaded below
            // continue at: reload + add
        }

        // reload after call
        v_i2 = stack[g.fp + 0x08]
        v_acc2 = stack[g.fp + 0x10]

        v_new_acc = i32.add(v_acc2, consume: v_result)

        fuel_check
        suspend:2 {
            stack[g.fp + 0x08] = v_i2
            stack[g.fp + 0x10] = v_new_acc
            stack[g.fp + 0x20] = 2u32
            ret SUSPENDED
        }
        resume:2 {
            v_i2 = stack[g.fp + 0x08]
            v_new_acc = stack[g.fp + 0x10]
            // continue at: i32.sub
        }

        v_one = i32.const 1
        v_new_i = i32.sub(v_i2, consume: v_one)

        fuel_check
        suspend:3 {
            stack[g.fp + 0x08] = v_new_i
            stack[g.fp + 0x10] = v_new_acc
            stack[g.fp + 0x20] = 3u32
            ret SUSPENDED
        }
        resume:3 {
            v_new_i = stack[g.fp + 0x08]
            v_new_acc = stack[g.fp + 0x10]
            // continue at: continue (loop back-edge)
        }

        continue (v_new_i, v_new_acc)
    } -> v_out

    ret consume: v_out
}
```

### Loop semantics

`loop (v_i, v_acc) { ... continue (v_new_i, v_new_acc) } -> v_out`

- The loop header binds two vregs: `v_i` and `v_acc`.
- `continue (v_new_i, v_new_acc)` is the back-edge — it rebinds
  the loop header vregs and jumps to the top.
- `break v_acc` exits the loop. The value becomes `v_out` (the
  loop's result binding after `}`).
- This is block-argument SSA in nested form: the back-edge
  "passes arguments" to the next iteration.

### Why inline beats bottom-grouped

1. **Context.** You see what's live, what gets stashed, and how to
   resume *right where it happens*. No scrolling to cross-reference
   `suspend:3` at the bottom with the code it guards.

2. **Branches read inline.** `br.if (v1) { ret v_ret }` — the
   taken path is right there. No scanning for labels.

3. **Resume is co-located.** Each `resume:N` sits next to its
   `suspend:N`. You can visually verify that the resume recipe
   reconstructs exactly what the suspend stub stashed.

4. **`consume:` makes lifetimes visible.** You scan for a vreg
   and immediately see where it dies.
