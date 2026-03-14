# Universal Stack ABI

This document records design decisions for the universal WASM stack ABI
that both the interpreter and JIT share. The goal: a suspended execution
state is a blob of bytes you can copy, serialize, send across a network,
and resume on a different machine, a different CPU architecture, or a
different execution mode (interpreter, JIT, or mixed).

---

## Design Goals

1. **Portable suspend/resume.** A computation suspended in the JIT on
   aarch64 can resume in the interpreter on x86_64, or vice versa.
2. **Version-stable.** A suspended stack from wust v1 can resume on
   wust v2. This enables live migration of long-running persistent
   WASM modules across nodes.
3. **Mode-agnostic.** Some functions can be JIT-compiled while others
   are interpreted. Mixed mode must work transparently — the stack
   format doesn't care how a function is executed.
4. **Serializable.** The stack is just bytes. No pointers, no native
   CPU state, no architecture-specific artifacts. If it's on the stack,
   it can be serialized.

---

## Frame Layout

Each function call gets a frame on the universal stack. All slots are
8 bytes (u64). The frame is fixed-size per function — sized for the
worst case across all suspend points (max operand depth is known at
compile time).

```
stack[fp + 0]       = header (func_idx + resume_point_id, packed)
stack[fp + 1]       = local_0
stack[fp + 2]       = local_1
...
stack[fp + N]       = local_{N-1}
stack[fp + N+1]     = operand_0     // live operand stack values
stack[fp + N+2]     = operand_1
...
```

### Frame header (1 slot, 8 bytes)

The header packs two values into a single u64:

- **func_idx**: identifies which function this frame belongs to. Needed
  to interpret the rest of the frame (local count, types, what the
  resume point means). Without this the frame is opaque bytes.
- **wasm_pc**: the WASM program counter (parsed instruction index) where
  execution was suspended. This is a property of the WASM module, not
  any particular engine. The universal resumer uses it to fast-forward
  to the target engine's nearest safe point.

Exact bit packing TBD (e.g. `func_idx: u32 | wasm_pc: u32`).

**Frame size is NOT stored in the frame.** It's statically derivable
from the function metadata (`1 + num_locals + max_operand_depth`). To
walk the stack, read each frame's func_idx, look up its size, advance.
This is O(n) but only happens on suspend/serialize — never on the hot
path.

### Locals

Params first, then declared locals. Count is fixed and known from the
function type + local declarations.

### Operands

Operand stack values live at the current safe point. The number of live
operands varies per resume point, but the *maximum* across all safe
points determines the frame size.

The frame size for a function is:
`1 + num_locals + max_operand_depth` slots (each 8 bytes).

---

## Safe Points, Resume Points, and the Universal Resumer

### The problem

Different execution engines define different "safe points" — places
where they can suspend and resume cleanly. The interpreter might suspend
at any opcode. The JIT only has suspend logic at calls and loop headers.
A future aarch64 JIT might have different safe points than a future
riscv JIT. Superinstructions fuse opcodes differently across versions.

If the resume point format is coupled to any engine's internal safe
point set, cross-mode and cross-version resume breaks.

### The solution: WASM PC + universal resumer

**The resume point is just the WASM program counter** — the index of the
instruction in the parsed bytecode where execution was suspended. This
is universally meaningful: it's a property of the WASM module itself,
not of any particular compiler or execution engine.

Each execution engine defines its own internal set of safe points (calls,
loop headers, whatever it needs). The ABI doesn't care what those are.

On resume, a **universal resumer** bridges the gap between the serialized
WASM PC and the target engine's safe points:

1. Load locals + operands from the serialized frame.
2. Start executing raw WASM opcodes from the saved PC — one by one, no
   fusion, no superinstructions, simplest possible stack machine.
3. Run until hitting a safe point the *target* execution engine
   recognizes.
4. Hand off to the target engine, which takes over from there.

### Why this works

- **Engines are fully decoupled from the ABI.** The JIT's safe points,
  superinstructions, and fusion strategies are invisible to the
  serialized format. Each engine is free to optimize however it wants.
- **Cross-version stable.** wust v2 can add/remove/change
  superinstructions freely. The serialized format is just WASM opcodes.
- **Cross-architecture stable.** An aarch64 JIT and an x86 JIT can have
  completely different safe point sets. The resumer bridges both.
- **Trivially correct.** The universal resumer is ~200 lines of the most
  naive stack-machine interpreter possible. No optimization, no fusion.
  Easy to audit, easy to test, executes for microseconds per frame on
  resume.
- **Negligible cost.** The resumer runs at most one basic block of
  straight-line opcodes per frame. It runs once per resume, on the cold
  path. Not a performance concern.

### What each engine must provide

Each execution engine (interpreter, JIT, future backends) only needs to
declare its own set of safe points — the instruction indices where it
can accept a handoff from the resumer. The engine doesn't need to know
about any other engine's safe points.

The operand stack depth at any WASM instruction is statically known from
WASM validation. So the resumer always knows exactly how many operand
values are live, regardless of where it's executing.

### Correctness testing: engines as mutual oracles

The universal resumer doubles as a **correctness oracle** for every
execution engine.

Set fuel to zero. Every engine runs exactly one step (from one safe
point to the next). After each step, serialize the frame and compare
across engines. Any mismatch in any slot = a bug.

This works for every combination: interpreter vs. resumer, JIT vs.
interpreter, aarch64 JIT vs. x86 JIT, any engine vs. any engine. Each
engine is every other engine's test harness — for free — just by virtue
of sharing the universal stack ABI.

You don't need to know which engine is wrong. You know they disagree,
you diff the frames slot by slot, and the divergence tells you exactly
what went wrong. The step size is each engine's own safe-point interval,
so every engine is tested at its natural granularity.

**Chaos engine testing.** The strongest form: randomly shuffle which
engine executes each safe-point-to-safe-point step. Instruction 1 on
the interpreter, instruction 2 on the JIT, instruction 3 back to the
interpreter, etc. The final output must be byte-identical to a clean
single-engine run every time.

If it is, you've proven the engines are not just individually correct
but *compositionally* correct — the state handoff at every single safe
point is perfect. No hidden assumptions about frame layout.

If it isn't, you've found a bug that only manifests at engine boundaries
— the kind that never shows up in normal testing. And you know exactly
which swap caused it from the frame diff after that specific handoff.

The test harness is trivial: randomly pick an engine for each step. A
few lines of code. The universal stack ABI makes it possible — no other
runtime can do this because nobody else has portable engine state.

---

## Calling Convention

### Who puts results where?

**The caller is responsible for picking up the callee's results.**

The callee writes its return values to a known location at the bottom
of its own frame. When the callee returns, the caller reads the results
from the callee's frame area and incorporates them into its own operand
stack / locals.

This decouples callee from caller completely:
- The callee doesn't need a pointer into the caller's frame.
- The callee doesn't know if the caller is interpreted or JIT-compiled.
- On suspend/resume, the callee can be resumed in a different execution
  mode without any knowledge of the caller's state.

### JIT locals-base register (g.lb)

The interpreter uses `wasm_fp.ptr` (past the header) and accesses locals via
**negative** byte offsets: `fp - (HEADER_SIZE + locals_size - byte_offset)`.

The JIT uses a **locals-base** register (`g.lb`, ARM64 x29) that points to
the start of the frame — before locals, before the header. All access uses
**positive** unsigned offsets from `g.lb`:

```text
[params][locals][FrameHeader 12B][operands...]
^g.lb           ^g.lb+locals_size ^g.lb+locals_header_size
```

**Why positive offsets?** ARM64's `ldr/str [Xn, #imm12]` with unsigned
immediate gives 0–16,380 bytes (4,095 i32s) of range with zero-cost
encoding. The negative-offset form (`ldur [Xn, #simm9]`) only covers
±256 bytes (~64 i32s). Since locals, header, and operands all live at
positive offsets from the frame start, `g.lb` gives the full range to
all of them. In practice the limit is unreachable — a function would
need thousands of locals plus deep operand stacks to exceed 16KB.

The entry trampoline converts between the two representations:
- **Entry:** `g.lb = wasm_fp.ptr - (locals_size + HEADER_SIZE)`
- **Exit/suspend:** `wasm_fp.ptr = g.lb + locals_size + HEADER_SIZE`

### Frame advance on calls

The caller's top-of-stack operands become the callee's parameters.
They occupy the same stack slots — the caller "pushes" args as
operands, and the callee sees them as `locals[0], locals[1], ...`
at the start of its frame:

```text
caller frame                                callee frame
[params][locals][header][op0][op1][arg0][arg1][decl locals][header][ops...]
^caller g.lb                     ^callee g.lb
                                  args = callee's params
```

The advance skips the caller's frame up to (but not including) the
args, because those args are now the callee's first locals:

```
advance = locals_header_size + (operand_depth[pc] - callee_param_slots) * 4
```

- `locals_header_size` — caller's `locals_size + HEADER_SIZE` (bytes)
- `operand_depth[pc]` — caller's operand stack depth **before** the
  call executes (in 4-byte slots, from the statically-known depth
  table). This includes the args about to be consumed.
- `callee_param_slots` — total slot count of the callee's parameters
  (`sum of slot_size per param`). Subtracted because those slots
  become part of the callee's frame, not the caller's.

Before call: `add g.lb, g.lb, #advance`
After return: `sub g.lb, g.lb, #advance`

This is per-call-site (not per-function max) because the
interpreter's `prev_fp_offset` is computed from the live `sp`, and
suspend/resume interop requires both engines to agree on frame
positions.

**TODO:** When a callee has more parameters than available CC
registers, overflow params will need to remain on the stack rather
than being moved into registers. The current scheme assumes all
params fit in registers.

### JIT hot path vs. host boundary

- **JIT-to-JIT calls:** Can use registers (x9-x15 etc.) as an
  optimization. This is purely internal to the JIT and invisible to
  the stack ABI. The stack is not touched on the hot path.
- **Host boundary (entry/exit):** Values go through the universal stack.
  The JIT loads args from the stack on entry and stores results to the
  stack on exit.
- **Suspend points:** The JIT flushes register state into the canonical
  frame format on the universal stack. This is the only time the JIT
  touches the stack — on the cold (suspend) path, never the hot path.

### Multi-value params and returns

**TODO:** Define how >7 values are handled. Options:

1. Always stack-based in the universal ABI; JIT loads first N into
   registers as an optimization.
2. Hybrid: first 7 in registers, overflow on the stack with a defined
   layout.

The universal ABI is stack-based regardless — the register optimization
is internal to JIT-to-JIT calls and not visible at the ABI level.

---

## Open Questions

- **Header bit packing:** `func_idx: u32 | wasm_pc: u32` is simple.
  Could pack tighter if needed. Need to decide on limits — is u16
  enough for func_idx (65k functions)? WASM spec allows u32 function
  indices. wasm_pc as u32 covers 4 billion instructions per function,
  which is more than enough.

- **Operand stack metadata:** At any WASM PC, the number and types of
  live operand values is statically known from WASM validation. A side
  table mapping (func_idx, wasm_pc) → operand layout would let a
  deserializer interpret frames without re-validating the bytecode.
  Alternatively, the universal resumer already needs to understand the
  bytecode — maybe it can derive this on the fly.

- **v128 (SIMD) values:** These are 16 bytes, not 8. Do they occupy two
  slots? That's what the current stack does, but it means the slot count
  for operands depends on value types, not just value count.

- **Back-pointer vs. forward-walk:** Currently no back-pointer in the
  frame header. Stack walking goes forward from the base. If profiling
  or debugging needs fast backward walks, we may revisit.

- **Resumer safe point registration:** How does each engine declare its
  safe points? A simple bitmap over instruction indices? A callback?
  A sorted list? The resumer needs to efficiently check "is this PC a
  safe point for the target engine?"
