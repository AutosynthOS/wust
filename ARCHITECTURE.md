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
