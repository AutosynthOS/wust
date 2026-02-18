# WUST — WebAssembly Runtime for Durable Agent Execution

## Problem

AI agents aren't stateless functions. They need to:
- Remember what happened last week
- Sleep for days and wake up exactly where they left off
- Hold persistent connections (Discord WebSocket, etc.)
- Execute untrusted user-defined code without escaping the sandbox

Standard serverless runtimes die between events. Compiled WASM runtimes (wasmtime/cranelift) achieve near-native speed but make mid-execution snapshotting extremely difficult — native CPU registers and stack frames don't map cleanly back to WASM's virtual state machine.

**WUST takes the opposite tradeoff**: explicit, always-serializable VM state. Performance is secondary to snapshot fidelity.

---

## Core Primitive: The Managed Stack

The central design insight: **the native execution stack and the snapshot format are the same bytes.** No conversion, no serialization, no frame walking. `memcpy` to save, `memcpy` to restore.

### Frame Layout

Each WASM function gets a fixed-size frame on a managed stack (not `rsp`):

```
+------------------------------+
|  resume_index: u32  [+0]     |  Portable ID (not a code pointer)
|  local $0: u32/i32  [+4]     |  WASM-typed values only
|  local $1: u32/i32  [+8]     |  No native pointers
|  local $2: u32/i32  [+12]    |  No architecture-specific state
|  ...                         |  Frame size varies per function
+------------------------------+
```

**resume_index** is a small integer, not a code pointer. The mapping from index to native address is rebuilt per-platform at load time:

```
Machine A (x86):     resume_table[1] = 0x55bf0
Machine B (arm64):   resume_table[1] = 0x4012a0
Machine C (riscv):   resume_table[1] = 0x81000
```

Same snapshot bytes, different table. Cross-platform migration is just a table swap.

### Call/Return via Direct Jumps

Native `call`/`ret` is replaced with `jmp` + managed stack manipulation:

**Call** (3-4 instructions, no push, no return address):
```asm
mov     dword ptr [r12], 1      ; write OUR resume_index
lea     ebx, [eax - 1]          ; compute argument
sub     r12, 16                 ; allocate callee frame
mov     [r12 + 4], ebx          ; write callee's parameter
jmp     fib_entry               ; direct jump (not call)
```

**Return**:
```asm
add     r12, 16                 ; pop frame
cmp     r12, r13                ; back to host boundary?
jge     host_return
mov     ecx, [r12]              ; load caller's resume_index
jmp     [resume_table + rcx*8]  ; dispatch to resume point
```

No RSB (Return Stack Buffer) usage. No code pointers on the managed stack. ROP attacks are structurally impossible against WASM-to-WASM calls.

---

## Suspend / Snapshot / Resume

### Suspend Mechanism

Every loop header and call site gets a suspend check:

```asm
test    byte ptr [r15], 1       ; read flag from memory
jnz     .suspend                ; branch if set (macro-fused, 1 uop)
```

The CPU macro-fuses `test+jnz` into a single uop. Branch prediction marks it "never taken" — effectively zero cost. Another thread sets the flag byte to trigger suspension.

Benchmarked overhead: **2-6%** on hot paths (vs 130%+ for a central handler approach, rejected).

### Snapshot

```rust
fn snapshot(managed_sp: *const u8, managed_base: *const u8) -> Vec<u8> {
    memory[sp..base].to_vec()  // that's it. memcpy.
}
```

### Resume

```rust
fn resume(snap: &[u8], managed_base: *mut u8, resume_table: &[*const u8]) {
    let sp = base - snap.len();
    copy(snap, sp);                              // restore stack
    let idx = read_u32(sp);                      // innermost resume_index
    jump_to(resume_table[idx], sp);              // continue execution
}
```

No frame walking. No register map consultation. No platform-specific logic.

### JIT Suspend Strategies

Two approaches for suspending compiled code:

**Strategy 1 — Zero-cost trap-based:** Run native code freely, use signal/trap to interrupt, then use code maps to identify the current WASM instruction. Copy remaining instructions to a trampoline page, finish the current logical WASM instruction, then jump to a handler that maps live registers to the universal stack format via dense code mapping tables. Zero hot-path overhead, but complex signal handling and architecture-specific code mapping.

**Strategy 2 — Inline test+jnz at safe points (recommended):** Insert `test+jnz` checks at loop headers and call sites. The branch predictor eliminates the cost (2-6% overhead benchmarked). Simple, portable, and sufficient for I/O-bound agent workloads where the function will immediately call a host import and block on network anyway.

Strategy 2 is recommended for initial implementation. Strategy 1 can be added later for compute-heavy modules where even 2% matters.

---

## Tiered Compilation

The resume index system enables seamless tiered execution:

```
resume_table[0..4]   = compiled    (hot main loop)
resume_table[5..12]  = interpreter (cold init code)
resume_table[13..20] = compiled    (hot request handler)
```

Interpreter and compiled code use the same managed stack, same frame layout, same resume indices. When a function gets hot (call count threshold), a background thread compiles it and atomically swaps resume table entries. No coordination needed — callers don't know or care whether the callee is interpreted or compiled.

### Unified Execution Interface

Both interpreter and JIT backends produce and consume the same snapshot format:

```rust
/// Universal state — both backends serialize to/from this.
struct Snapshot {
    memory: Vec<u8>,
    globals: Vec<Value>,
    tables: Vec<Vec<Option<u32>>>,
    frames: Vec<FrameSnapshot>,  // innermost last
}

struct FrameSnapshot {
    func_idx: u32,
    wasm_pc: u32,       // WASM instruction index (not native PC, not Op index)
    locals: Vec<Value>,
    operand_stack: Vec<Value>,
}
```

The execution backend trait:

```rust
trait ExecutionBackend {
    fn call(
        &mut self,
        store: &mut Store,
        func_idx: u32,
        args: &[Value],
    ) -> Result<CallOutcome, ExecError>;
}

enum CallOutcome {
    Return(Vec<Value>),
    Suspended(Snapshot),
    HostCall { func_idx: u32, args: Vec<Value> },
}
```

The `HostCall` variant is how durable I/O works — when agent code calls `sleep("1 day")`, the backend returns `HostCall`, the orchestrator snapshots and suspends.

### Per-Function Dispatch

```rust
enum FuncBackend {
    Interpreted,
    Compiled(*const u8),
}

// Tiering logic:
// call_counts[idx] += 1
// if call_counts[idx] == TIER_THRESHOLD: queue_for_compilation(idx)
```

When compiled code calls an interpreted function (or vice versa), a trampoline bridges the boundary. Both use the same `Store` and snapshot format.

---

## Benchmark Results

fib(30) x 1000 iterations, hand-written x86_64 assembly:

| Variant                          | Time   | vs Native        |
| -------------------------------- | ------ | ---------------- |
| Native (call/ret, push/pop)      | 3.34ms | baseline         |
| Managed stack (jmp dispatch)     | 3.10ms | **-7% faster**   |
| Managed + suspend (test+jnz)     | 2.97ms | **-10% faster**  |
| Managed + central handler (call) | 7.85ms | +135% (rejected) |

The managed stack is faster than native because it replaces implicit push/pop/call/ret (6 stack ops + indirect RSB branch per frame) with explicit sub/mov/jmp (3 ops + direct branch).

---

## Security Properties

| Attack                            | Native Stack          | Managed Stack                                                            |
| --------------------------------- | --------------------- | ------------------------------------------------------------------------ |
| ROP (Return-Oriented Programming) | Vulnerable            | **Immune** — no code pointers on stack                                   |
| Spectre-RSB                       | Vulnerable            | **Immune** — no RSB usage                                                |
| Stack buffer overflow -> hijack   | Return addr corrupted | resume_index corrupted -> wrong but valid resume point (still sandboxed) |

Worst case with corrupted resume index: execution jumps to a valid resume point with wrong locals. Produces garbage but cannot escape the WASM sandbox.

New attack surface: malicious snapshots can set any local to any value and resume at any valid point. Mitigated with HMAC authentication for network migration.

---

## Split Stack (Planned)

Separate control stack (resume indices) from data stack (locals):

```
Control stack:  [idx][idx][idx][idx]...     4 bytes each, uniform
Data stack:     [===12 bytes===][==8 bytes==][====32 bytes====]...
                    fib's locals   add's locals  complex's locals
```

Benefits:
- **Partial snapshots**: Control stack alone = complete call chain (~40 bytes for 10-deep). Useful for scheduling metadata.
- **Hardware-enforced CFI**: Control stack on a separate page, `mprotect` read-only during function bodies.
- **Compression**: Control stack is small integers with heavy repetition — compresses 50:1 for recursive code.

---

## The Platform Stack

```
discord.js / agent code     (JS/TS — user-facing)
        |
Node.js polyfills           (JS + native bindings — sandboxed realm)
        |
Boa.js engine               (Rust JS interpreter, compiled to WASM)
        |
WUST runtime                (executes Boa's WASM module)
        |
Host imports (WIT)          (TCP, HTTP, WebSocket, timers, crypto)
        |
Host OS                     (actual sockets, TLS, etc.)
```

### Durable Functions

The magic primitive: `await sleep("1 day")`

1. Agent hits the sleep call
2. Runtime checkpoints entire WASM + Boa state to durable storage
3. Instance is suspended (zero resources consumed)
4. 24h later, state is reloaded, execution continues from exactly where it stopped

### Durable WebSockets

The runtime owns persistent connections (Discord WS, etc.) at the infrastructure level. Incoming events route to the correct agent instance, waking it from checkpoint if needed. Agents don't manage sockets — they receive events through a clean API.

### Execution Model

```
Event -> Router -> Find/Resume Agent WASM -> Execute -> Checkpoint -> Suspend
```

### Security Model

All I/O is gated through runtime host imports. Agents call `socket.connect(host, port)` and the runtime decides whether to allow it based on declared permissions. WASM can't escape the sandbox. Agents receive events and call tools — no raw filesystem, no raw DB, no raw network.

---

## WIT Host Interfaces

WIT (WebAssembly Interface Types) defines the typed boundary between guest modules and host capabilities.

### Core Host Interfaces

```wit
package autosynth:host;

interface tcp {
    type stream-id = u32;

    connect: func(host: string, port: u16) -> result<stream-id, string>;
    write: func(stream: stream-id, data: list<u8>) -> result<u32, string>;
    read: func(stream: stream-id, max-bytes: u32) -> result<list<u8>, string>;
    close: func(stream: stream-id);
}

interface tls {
    upgrade: func(stream: tcp.stream-id, hostname: string) -> result<tcp.stream-id, string>;
}

interface timers {
    type timer-id = u32;

    set-timeout: func(ms: u64) -> timer-id;
    clear-timeout: func(id: timer-id);
}

interface http {
    record request {
        url: string,
        method: string,
        headers: list<tuple<string, string>>,
        body: option<list<u8>>,
    }

    record response {
        status: u16,
        headers: list<tuple<string, string>>,
        body: list<u8>,
    }

    fetch: func(req: request) -> result<response, string>;
}

interface discord {
    send-message: func(channel-id: string, content: string) -> result<string, string>;
    next-event: func() -> event;
}

world agent {
    import autosynth:host/tcp;
    import autosynth:host/tls;
    import autosynth:host/timers;
    import autosynth:host/http;
    import autosynth:host/discord;
    export run: func() -> result;
}
```

### Canonical ABI

The canonical ABI lifts/lowers between component-level types (strings, records, lists) and core WASM linear memory. This replaces the current raw `HostFunc` signatures with typed interfaces.

---

## Milestone 1: Discord Bot on Boa + WUST

The first concrete demo target: a discord.js bot running inside Boa.js (compiled to WASM) inside WUST.

### What discord.js Needs

| Capability    | Node Module              | What It Does                             | Implementation         |
| ------------- | ------------------------ | ---------------------------------------- | ---------------------- |
| WebSocket     | `ws` -> `node:net`       | Discord Gateway (persistent connection)  | Host TCP+TLS imports   |
| HTTP requests | `node:https` / `undici`  | REST API (send messages, fetch channels) | Host HTTP imports      |
| Event system  | `node:events`            | EventEmitter                             | Pure JS polyfill       |
| Buffers       | `node:buffer`            | Binary data handling                     | Pure JS polyfill       |
| URL parsing   | `node:url`               | URL construction/parsing                 | Pure JS polyfill       |
| Timers        | `setTimeout/setInterval` | Heartbeat, rate limiting                 | Host timer imports     |
| Zlib          | `node:zlib`              | Gateway compression                      | Optional (can disable) |
| Crypto        | `node:crypto`            | Token handling                           | Minimal host import    |

### Node.js Polyfill Tiers

**Tier 0 — Pure JS polyfills (no host interaction):**
- `node:events` — EventEmitter (~100 lines of JS)
- `node:buffer` — Buffer over ArrayBuffer/Uint8Array
- `node:url` — URL parsing
- `node:util` — promisify, format, inherits

These run entirely inside Boa. No WASM boundary crossing.

**Tier 1 — Thin host bindings:**
- `setTimeout` / `setInterval` / `clearTimeout` — host manages timer queue
- `console.log` / `console.error` — trivial host import

**Tier 2 — TCP/TLS/HTTP/WS (the real work):**

Host provides raw TCP/TLS capabilities via WIT imports. Node polyfills build on top:

```js
// Inside the polyfill realm (user code cannot access directly)
class Socket extends EventEmitter {
    connect(port, host) {
        this._streamId = __host_tcp_connect(host, port);
        this.emit('connect');
    }
    write(data) {
        __host_tcp_write(this._streamId, data);
    }
}
```

`node:http`, `node:https`, and the WebSocket implementation are JS polyfills that use these native Socket bindings.

### The Event Loop

discord.js expects an async event loop. The execution model inside the WASM module:

```
loop {
    // 1. Run all pending JS microtasks (promise callbacks)
    boa.run_jobs();

    // 2. Poll host for ready events (timers, data, connections)
    let events = host_poll_events();  // WIT call

    // 3. Dispatch events into JS land
    for event in events {
        match event {
            TimerFired(id)           => fire JS callback,
            DataReady(stream, bytes) => emit 'data' on Socket,
            WsClosed(stream)         => emit 'close' on WebSocket,
        }
    }

    // 4. Nothing pending? This is the snapshot/suspend point.
    if no_pending_work {
        host_suspend();  // checkpoint and sleep
    }
}
```

This event loop lives inside the WASM module (Boa's Rust code compiled to WASM). `host_poll_events()` crosses the WASM boundary into WUST host imports.

### Build Sequence

1. **Boa compiling to WASM, running in WUST** — `console.log("hello")` end-to-end
2. **Timer host imports** — `setTimeout` working = event loop working
3. **TCP host imports** — raw connect/read/write, test with simple HTTP GET
4. **`node:http` polyfill** — enough for Discord REST API calls
5. **WebSocket polyfill over TCP+TLS** — gets the Discord Gateway working
6. **Wire up discord.js** — should "just work" (tell Discord not to compress to skip zlib)

Step 1 is the keystone that validates the entire stack.

---

## WASM-Based Code Splitting (Future)

Static call graph analysis + dynamic snapshot state enables automatic program decomposition:

```
Full module:     500KB code, 2MB state (after init)
  handler_a:      30KB code, 4KB state (only reachable code)
  handler_b:      45KB code, 50KB state
  handler_c:       5KB code, 100B state
```

Functions used during init but never after are dead from the handler's perspective. Copy-on-write instantiation shares snapshot bytes across instances.

---

## Open Work

### Spec Compliance
- [x] Core MVP (all instructions)
- [x] Sign extension, non-trapping float-to-int, multi-value
- [x] Bulk memory ops (memory.init, memory.copy, memory.fill, data.drop)
- [x] Table ops (table.get/set/grow/size/copy/fill)
- [x] Reference types (ref.is_null, ref.null, ref.func)
- [x] Passive data and element segments
- [ ] Imports / multi-module linking
- [ ] Tail calls (return_call, return_call_indirect)
- [ ] SIMD (v128 operations)
- [ ] GC / typed function references
- [ ] Threads / atomics
- [ ] Exception handling

### Runtime Architecture
- [ ] Unified execution backend trait (interpreter + JIT)
- [ ] Snapshot / resume for interpreter
- [ ] Baseline single-pass JIT compiler (managed stack convention)
- [ ] Tiered compilation (interpret cold, compile hot)
- [ ] ARM64 / RISC-V ports
- [ ] Split stack prototype
- [ ] Snapshot HMAC authentication

### Platform
- [ ] WIT / Component Model support
- [ ] WASI host I/O layer
- [ ] Boa.js compiled to WASM, running in WUST (Milestone 1 keystone)
- [ ] Node.js polyfills (events, buffer, url, util)
- [ ] Host TCP/TLS/HTTP/timer imports
- [ ] WebSocket polyfill
- [ ] discord.js running end-to-end (Milestone 1 complete)
- [ ] Durable WebSocket infrastructure
- [ ] Event router and agent lifecycle
- [ ] Code splitting via call graph analysis
