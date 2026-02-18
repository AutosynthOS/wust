# wust

A WebAssembly runtime with a managed execution stack. WUST decodes WASM bytecode once at parse time into a custom instruction representation, then interprets it on an explicit stack (not the native CPU stack). This makes mid-execution snapshots trivial — frame state is just integers and values, portable across architectures.

## Modules

| Module | Purpose |
|---|---|
| `runtime::module` | Parsed WASM module — holds function signatures, type definitions, memory/table/global declarations, exports, and imports. Immutable after construction. |
| `runtime::instruction` | Custom instruction enum decoded from WASM bytecode at parse time. Covers control flow, memory ops, arithmetic, and more. |
| `runtime::store` | Mutable runtime state — memory pages, globals, tables, and constant expression evaluation. |
| `runtime::exec` | Core interpreter. Drives instruction execution on the managed stack with explicit frames and labeled branch targets. |
| `runtime::value` | WASM value enum (`I32`, `I64`, `F32`, `F64`, `V128`, `FuncRef`) with typed accessors. |
| `runtime::jit` | (Disabled) Experimental JIT compiler for aarch64/Apple Silicon. |

## Common Commands

```sh
# Run all spec tests
cargo test -p wust

# Run a specific test
cargo test -p wust spec_i32

# Run the fibonacci benchmark
cargo run -p wust --example bench_fib --release

# Build in release mode
cargo build -p wust --release
```

## Tests

`tests/spec_tests.rs` runs the official WebAssembly spec test suite via `.wast` files. Currently 84 tests pass with 13 ignored (GC/type-recursion proposals not yet implemented).
