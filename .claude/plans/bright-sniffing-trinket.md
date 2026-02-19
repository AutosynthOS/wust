# Plan: Run `console.log("hello world")` in Plasma inside WUST

## Context

Plasma compiles to `wasm32-unknown-unknown` and exports `alloc` and `eval`. It imports `host_log(ptr, len)` from the host. WUST is our WASM interpreter. The goal: compile plasma → .wasm, load it into wust, call `eval` with JS source `console.log("hello world")`, and verify the output reaches the host.

## Key Problem: HostFunc Can't Read Memory

The current `HostFunc` signature is:
```rust
pub type HostFunc = Box<dyn Fn(&[Value]) -> Vec<Value>>;
```

When plasma calls `host_log(ptr, len)`, the host function gets `ptr` and `len` as i32 values but **cannot read the WASM linear memory** to extract the actual string. We need to pass memory access to host functions.

## Step 1: Extend `HostFunc` to receive `&[u8]` memory

**Change** the type in `crates/wust/src/runtime/store.rs:82`:
```rust
pub type HostFunc = Box<dyn Fn(&[Value], &[u8]) -> Vec<Value>>;
```

**Update call sites** in `crates/wust/src/runtime/exec.rs`:
- `call_host_fn` (line 436): pass `&store.memory` as second arg
- Direct host call at line 505: `Ok(host_fn(args, &store.memory))`
- All `call_host_fn` invocations (lines 637, 659, 668)

**Update all existing closures** in `crates/wust/tests/spec_tests.rs` to accept `_memory: &[u8]` — they just ignore it.

## Step 2: Fix the getrandom problem

Plasma currently depends on `getrandom` with `wasm_js` feature, which expects JavaScript's `crypto.getRandomValues`. WUST is a bare host, not a browser.

**Options:**
1. Use `getrandom` `custom` feature + host-provided `random_fill` import
2. Use a deterministic PRNG seeded from a host import
3. Remove `getrandom` dependency if Boa doesn't strictly need it

**Recommended:** Investigate whether Boa actually needs randomness at init time. If it does, switch to `custom` getrandom with a host-provided `random_fill(ptr, len)` import.

## Step 3: Build plasma.wasm

The test/example compiles plasma as a subprocess:
```
cargo build -p plasma --target wasm32-unknown-unknown --release
```

Output at: `target/wasm32-unknown-unknown/release/plasma.wasm`

## Step 4: Write the integration example

**File:** `crates/wust/examples/plasma_hello.rs`

Algorithm in plain English:

1. Build plasma.wasm by invoking cargo as a subprocess (or load pre-built)
2. Read the `.wasm` bytes from disk
3. Parse: `Module::from_bytes(&wasm_bytes)`
4. Create a `Arc<Mutex<String>>` to capture log output
5. Build `host_log` host function: reads `ptr` (arg 0) and `len` (arg 1) from args, slices `memory[ptr..ptr+len]`, converts to UTF-8, appends to captured output
6. Build any other needed host functions (e.g. `random_fill`)
7. Create store: `Store::new_with_imports(&module, host_funcs, vec![])`
8. Call `alloc(source_len)` → get pointer `ptr`
9. Write JS source bytes into `store.memory[ptr..ptr+len]`
10. Call `eval(ptr, len)` → expect return `I32(0)`
11. Print / assert the captured output equals `"hello world"`

## Step 5: Raise or make configurable MAX_STEPS

`MAX_STEPS = 100_000_000` may not be enough for Boa's JS engine initialization. Either raise it significantly (e.g. 10 billion) or make it configurable via an `ExecConfig` passed to `invoke`.

## Files to modify

| File | Change |
|------|--------|
| `crates/wust/src/runtime/store.rs` | Change `HostFunc` type signature |
| `crates/wust/src/runtime/exec.rs` | Pass `&store.memory` to all host function calls |
| `crates/wust/tests/spec_tests.rs` | Update all `HostFunc` closures for new signature |
| `crates/plasma/Cargo.toml` | Fix getrandom dependency for bare wasm host |
| `crates/plasma/src/lib.rs` | Possibly add custom getrandom provider |
| `crates/wust/examples/plasma_hello.rs` | **New** — integration example |

## Verification

1. `cargo test -p wust` — all existing spec tests still pass (HostFunc signature change is backwards-compatible after updating closures)
2. `cargo build -p plasma --target wasm32-unknown-unknown` — compiles successfully
3. `cargo run -p wust --example plasma_hello` — prints "hello world"

## Open Questions

1. Does Boa actually need `getrandom` at init? If not, we can remove the dep entirely.
2. Will `MAX_STEPS` be sufficient, or do we need to make it configurable first?
3. Does the Boa fork compile cleanly for `wasm32-unknown-unknown` without additional patches?
