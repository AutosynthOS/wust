WASM_TARGET := wasm32-unknown-unknown
RELEASE_DIR := target/$(WASM_TARGET)/release

# Core plasma module (no wasm-bindgen stubs)
$(RELEASE_DIR)/plasma.wasm: crates/plasma/src/lib.rs crates/plasma/Cargo.toml
	cargo build -p plasma --target $(WASM_TARGET) --release

# Wrap the core module into a WebAssembly Component
$(RELEASE_DIR)/plasma.component.wasm: $(RELEASE_DIR)/plasma.wasm crates/plasma/wit/world.wit
	wasm-tools component new $< --wit crates/plasma/wit -o $@

.PHONY: plasma plasma-component clean

## Build the core plasma wasm module.
plasma: $(RELEASE_DIR)/plasma.wasm

## Build the plasma component (wraps core module with WIT).
plasma-component: $(RELEASE_DIR)/plasma.component.wasm

## Remove build artifacts.
clean:
	cargo clean
