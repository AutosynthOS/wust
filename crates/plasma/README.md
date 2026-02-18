# plasma

A JavaScript runtime that compiles to WebAssembly and runs inside WUST. Built on [Boa](https://github.com/boa-dev/boa) (Albert's fork with combined fixes).

Plasma exposes a minimal C ABI — `alloc` and `eval` — so the host (WUST) can pass JS source strings into the WASM module and get them evaluated.

## How It Works

1. The host calls `alloc(size)` to reserve space in Plasma's linear memory
2. The host writes a UTF-8 JS string into that memory
3. The host calls `eval(ptr, len)` which creates a Boa `Context`, evaluates the source, and returns `0` (success) or `1` (error)
4. `console.log` inside JS calls back to the host via the imported `host_log(ptr, len)` function

## Common Commands

```sh
# Build the WASM module
cargo build -p plasma --target wasm32-unknown-unknown

# Build optimized
cargo build -p plasma --target wasm32-unknown-unknown --release

# Check without building
cargo check -p plasma --target wasm32-unknown-unknown
```

## Output

The compiled WASM binary lands at:
```
target/wasm32-unknown-unknown/debug/plasma.wasm    # ~100MB debug
target/wasm32-unknown-unknown/release/plasma.wasm  # much smaller
```
