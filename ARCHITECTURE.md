# WUST Runtime Architecture

## Overview

WUST is a WebAssembly runtime designed around **performant resumability** —
the ability to suspend, snapshot, serialize, and resume wasm instances
across threads, time, and machines.

## Core Concepts

### Engine

Shared configuration and validation rules. "What dialect of wasm do we
support?" Holds feature flags, creates validators. No runtime state — it's
a factory for parsing and validating modules.

### Module

Compiled, validated, immutable wasm code. A blueprint. "Here's a program
that *could* run." Has no memory, no state, no identity. You can't call it.
Parse once, instantiate many times.

### Instance

A living, running (or paused) program. Owns its memory, globals, tables,
stack, and PC. This is the unit of execution, isolation, suspension, and
resumability. One module can produce many independent instances.

Because instances own their entire execution state as plain data (no Rust
stack frames, no pointers), they are:
- **Serializable** — snapshot at any suspension point
- **Send** — move across threads
- **Resumable** — deserialize and continue execution

### Linker

Resolves imports at instantiation time. Maps import names to concrete
implementations (host functions, other instance exports). Configuration
for wiring modules together — does not own or execute anything.

### Component

An orchestrator above core modules. Contains core modules, instantiates
them, wires them together, and exposes a typed interface via the Canonical
ABI (`canon lift` / `canon lower`). Components add rich types (strings,
records, variants, resources) on top of core wasm's i32/i64/f32/f64.

A component instance is a set of core instances + a typed calling
convention on top. It has no memory or execution state of its own.

## Layered Runtime Architecture

```
┌──────────────────────────────────────────────────┐
│  Host (Rust process)                             │
│  - raw OS APIs (net, fs, timers)                 │
│  - wasm runtime engine                           │
│                                                  │
│  ┌─────────────────────────────────────────────┐ │
│  │ Kernel Component (privileged)               │ │
│  │ - module management (load/unload)           │ │
│  │ - instance lifecycle (start/sleep/wake)      │ │
│  │ - capability grants                         │ │
│  │ - command socket for admin                  │ │
│  └──────────────┬──────────────────────────────┘ │
│                 │                                 │
│  ┌──────────────▼──────────────────────────────┐ │
│  │ System Components (semi-privileged)         │ │
│  │ - tcp proxy (shared listeners)              │ │
│  │ - fs proxy (sandboxed paths)                │ │
│  │ - timer service                             │ │
│  └──────────────┬──────────────────────────────┘ │
│                 │ WIT interfaces                  │
│        ┌────────┼────────┐                        │
│      ┌─▼──┐  ┌─▼──┐  ┌──▼─┐                     │
│      │ U1 │  │ U2 │  │ U3 │  (user instances)   │
│      └────┘  └────┘  └────┘                     │
└──────────────────────────────────────────────────┘
```

### Layers

**Host** — the Rust process. Provides raw OS APIs and runs the wasm engine.
Exposes a minimal, dumb API to the kernel component.

**Kernel Component** — wasm itself, but with privileged host imports. Manages
the lifecycle of all other components: load modules, instantiate, grant
capabilities, suspend/resume instances. Communicates with the host over a
direct command socket (load this, run that, list modules, set timer, etc.).

**System Components** — semi-privileged wasm components that act as
capability-based proxies for OS resources. Examples:
- **TCP proxy** — manages shared listeners, routes connections to user
  instances by host/address. Multiple users can listen on different virtual
  hosts via a single real listener.
- **FS proxy** — gives each user a sandboxed directory. Translates
  user paths to real paths within their allowed folder.
- **Timer service** — manages timers, wakes sleeping instances.

**User Components** — untrusted user code. Can only access system resources
through WIT interfaces exposed by system components. Cannot access
privileged kernel APIs.

### Capability-Based Security

Each layer only sees what it's been granted:
- Kernel gets raw host APIs
- System components get scoped capabilities from the kernel
- User components get scoped capabilities from system components
- User components cannot access each other's state

## Async & Sleep/Wake Model

### Resources Are Just Integers

In the component model, resources (tcp-listener, tcp-stream, file-handle)
are opaque i32 handles. The actual state (real OS sockets, file descriptors)
lives in the system component or host. User modules only hold integer
handles in their resource tables.

This means user module state is fully serializable — no actual OS resources
need to be captured, just integers that reference them.

### The Sleep/Wake Flow

```
User module starts up:
  1. Calls system import: tcp.listen("myapp.com:8080")
  2. System component binds a real socket, gives user handle 3
  3. User calls: handle_3.accept()  →  returns a future
  4. Compiled async runtime (tokio→wasm) polls it, gets Pending
  5. No other tasks → calls task.wait (component model's epoll)
  6. Runtime observes: module is parked, nothing ready
  *** Sleep point — snapshot and evict, or keep idle in memory ***

Connection arrives:
  7. Host OS: TCP connection on the real socket
  8. Host notifies system component
  9. System component resolves the pending future for user module
  10. Runtime resumes user instance (deserialize if tombstoned)
  11. task.wait returns, async runtime polls future → gets tcp-stream handle
  12. User code processes the HTTP request
  13. Done → back to task.wait → sleep again
```

### Suspension Points

An instance can be suspended whenever it calls `task.wait` with no ready
events. At that point:
- The flat interpreter's state (stack, PC, locals) is plain data
- Memory is a byte array
- Globals are plain values
- Resource tables are integer maps

All serializable. The instance can be:
- **Kept idle** in memory (cheap sleep, fast wake)
- **Snapshotted** to disk/network (deep sleep, slower wake, frees memory)
- **Migrated** to another machine (deserialize and resume)

### Interrupt / Kill

An atomic flag (e.g., `Arc<AtomicBool>`) is shared between the instance and
the runtime. The interpreter checks it periodically (at branches, calls, or
every N instructions). External threads can set it to signal:
- Time limit exceeded → trap
- Graceful shutdown → suspend at next safe point
- Priority preemption → park and schedule something else

## Design Decisions

### No Shared Store

Unlike wasmtime's `Store<T>` pattern (where the store owns all instance
state and instances are just handles), WUST instances own their own state
directly. This gives us:
- Simpler API: `instance.call("foo", args)` instead of
  `instance.call(&mut store, "foo", args)`
- Natural Send semantics: move an instance = move all its state
- Clean serialization boundary: one instance = one serializable blob

The tradeoff is that cross-instance shared memory (rare in practice)
would need explicit handling if ever needed.

### Flat Interpreter

The interpreter uses a flat loop with no Rust recursion. All execution
state lives on an explicit wasm stack (values, locals, inline frames).
This is critical for:
- No native stack overflow on deep wasm call chains
- Execution state is plain data, not Rust stack frames
- Serializable at any point for suspension/resumption
- Future JIT compatibility (clean stack layout)

---

## Implementation State (Current)

### Crate Layout

```
wust-core/          Low-level primitives (no WASM parsing dependency)
  context.rs        Empty Context struct (will hold g.ctx state)
  fibre.rs          FibreStack — guard-paged mmap for JIT return addresses
  instance.rs       Instance (Box<InstanceInner>) — all live runtime state
  mmap.rs           MmapRegion — shared mmap+guard page allocation
  stack.rs          Stack — managed wasm operand/frame stack (the snapshot format)
  value.rs          Val, WasmArgs, WasmResults

wust-codegen/       Code generation (architecture-specific, no runtime)
  emit.rs           AArch64 instruction emitter
  ir.rs             IR (virtual register SSA)
  lower_aarch64.rs  IR → AArch64 lowering, trampolines, fuel checks
  disasm.rs         Disassembly renderer (inspect feature)

wust/               Runtime (ties everything together)
  instance/         Re-exports wust_core::Instance + interpreter call fns
  interpreter/      Recursive interpreter (reference implementation)
  jit/              JIT compiler, call_dynamic, call_trampoline
  module/           Module parsing (wasmparser)
  parse/            WASM function/opcode parsing
```

### Instance & Module Separation

Instance does NOT own the Module. Module is passed separately to calls.

```rust
// wust-core
struct Instance { inner: Box<InstanceInner> }

struct InstanceInner {
    stack: Stack,        // managed wasm stack (THE snapshot format)
    fibre: FibreStack,   // JIT return address stack (separate from native sp)
    context: Context,    // g.ctx — will hold host/runtime pointers
}
```

Why Box: Instance gets stored in vecs, moved between scheduler slots.
A single pointer is cheaper than moving structs with mmap pointers.

Why no Module: Modules are shared across instances (many instances of
the same module). Instance is pure runtime state.

### Register Convention (AArch64)

```
x29  (g.fp)    Frame pointer into the managed wasm stack
x21  (g.fuel)  Fuel counter (i64, can go negative)
x20  (g.ctx)   Context pointer (unused currently, reserved)
x28            Saved host SP (during JIT execution, sp = fibre stack)
x9-x15         Scratch / param / result registers (caller-saved)
sp             During JIT: points to fibre stack (NOT native stack)
```

### Stack Pointer Swap

On JIT entry, the Rust inline asm trampoline:
1. Saves host callee-saved regs (x29, x30, x20, x21, x28) on host stack
2. `mov x28, sp` — save host SP
3. `mov sp, fibre_top` — switch to fibre stack
4. Sets up g.fp, g.fuel, calls trampoline
5. On return: `mov sp, x28` — restore host SP
6. Restores host regs

All `str x30, [sp, #-16]!` in function prologues automatically save
to the fibre stack. Zero codegen changes needed.

### Frame Layout

```
+0   frame header slot 0  (reserved — will hold resume_index)
+8   frame header slot 1  (reserved — will hold prev_fp or flags)
+16  local/param slot 0
+24  local/param slot 1
...
```

FRAME_HEADER_SIZE = 16 bytes (2 × u64 slots). Currently zeroed/unused.

---

## Suspend / Resume Design

### Outcome (Low-Level Primitive)

```rust
enum Outcome {
    Return,         // function returned normally, results in frame slots
    Suspended,      // fuel exhausted, state materialized to managed stack
    HostCall(u32),  // host import called, import index + args in frame
}
```

This is like `Poll<T>` in Rust's async — the scheduler uses it to
drive instances. Most users never see it.

### Two Suspend Triggers

1. **Fuel exhaustion** — cooperative scheduling. Refuel and resume.
2. **Host call** — async I/O. Resume when host operation completes.

Both are structurally identical from the JIT's perspective:
1. Materialize live registers → frame slots
2. Write `resume_index` into frame header
3. Return to host with Outcome variant

### Resume

1. Read `resume_index` from top frame
2. Look up native address: `resume_table[index]`
3. Load values from frame slots into registers
4. Continue execution

Resume table is per-compilation, per-architecture. Same snapshot
bytes, different table. Cross-machine migration = table swap.

### API Layers

**Low-level (scheduler/runtime internals):**
```rust
loop {
    match jit.poll(&module, &mut instance)? {
        Outcome::Return => break,
        Outcome::Suspended => instance.refuel(budget),
        Outcome::HostCall(idx) => {
            handle_import(idx, &mut instance).await;
        }
    }
}
```

**High-level (user-facing):**
```rust
let result = scheduler.run(&module, &mut instance, "handler", &args).await;
```

User never sees Suspended. The scheduler handles fuel management,
instance switching, and host call dispatch internally. The OS
naturally pages idle instances to disk swap — explicit serialization
is only needed for cross-machine migration or durable persistence.

### Component Model & Async

Core WASM is fully synchronous. The component model adds async via
canonical built-ins:

- `task.wait` — block until a subtask completes
- `task.poll` — non-blocking check
- `task.yield` — cooperative yield
- `stream.read` / `stream.write` — streaming I/O

These are defined at the component level as `canon task.wait` etc.
The component model **lowers them into core WASM imports** when
instantiating a component. By the time code reaches our
JIT/interpreter, `task.wait` is just a call to an imported function.

So `task.wait` = host call = suspend point. Same machinery as fuel
exhaustion. The scheduler registers interest with the OS
(epoll/kqueue), runs other instances, resumes when I/O completes.

```
future<T>  →  start async op, get subtask handle, task.wait, read T
stream<T>  →  stream.read/write, each can async via task.wait
```

For Rust async compiled to WASM: instead of calling epoll_wait on
the OS, the async runtime calls task.wait on the component model.
Same pattern, different layer. All I/O goes through host imports.

---

## Next Steps

### Immediate
- [ ] Define Outcome enum and poll/resume API
- [ ] Codegen: at suspend points, materialize registers → frame slots
- [ ] Codegen: write wasm_pc into frame header
- [ ] Codegen: emit resume entry points (load slots → registers)
- [ ] Build safe point table (wasm_pc → native address mapping per engine)
- [ ] Wire up poll() — call returns Outcome instead of assuming Return
- [ ] Host call mechanism (imported functions trigger suspend)
- [ ] Context struct gets useful fields (safe point table ptr, etc.)

### Universal Resumer & wust-core Migration
- [ ] Move module parsing/validation into wust-core (no superinstructions)
- [ ] Build universal resumer in wust-core — a minimal canonical WASM
      stack machine interpreter that operates at the raw WASM instruction
      level. Purpose: bridge between engines on resume. When resuming from
      a serialized wasm_pc that isn't a safe point in the target engine,
      the resumer executes atom instructions one-by-one until it reaches
      a safe point the target engine recognizes, then hands off. See
      `crates/wust/abi.md` for full design.
- [ ] Each engine (interpreter, JIT) declares its safe points — the set
      of wasm_pc values where it can accept a handoff from the resumer
- [ ] Chaos engine testing: randomly shuffle which engine executes each
      safe-point-to-safe-point step, verify byte-identical output

### Future
- [ ] Scheduler / executor (manages multiple instances)
- [ ] Component model integration (task.wait → host call → suspend)
- [ ] Snapshot serialization (memcpy of stack region)
- [ ] Cross-machine resume (safe point table swap)
- [ ] Tiered compilation (interpreter cold, JIT hot, same stack ABI)
