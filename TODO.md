# Component Model Runtime — TODO

## Track A: Test Harness Honesty + Coverage

### A1. Tighten assertion handlers — DONE
- [x] `AssertInvalid` that passes validation -> **fail**, not skip
- [x] `AssertUnlinkable` that instantiates successfully -> **fail**, not skip
- [x] `AssertMalformed` that parses successfully -> **fail**, not skip
- [x] `AssertTrap(Wat)` encode errors now count as failures, not passes
- [x] `Module` directive instantiation failures now count as skips with diagnostics

### A2. Named definition + instance registry — DONE
- [x] `definitions: HashMap<String, Vec<u8>>` in `ComponentTestRunner`
- [x] `named_instances: HashMap<String, usize>` + `instances: Vec<ComponentInstance>`
- [x] `ModuleDefinition`, `ModuleInstance`, `Register` directives handled
- [x] `invoke_component` supports named instance dispatch via `module_name: Option<&str>`

### A3. Wasmtime-specific validation — DONE
- [x] Reject root-level component imports (importing another component)
- [x] Reject root-level component exports (exporting inner component)
- [x] Reject reexport of imported function without implementation
- [x] Reject type nesting deeper than 100 levels

---

## Track B: Runtime Correctness — DONE

### B1. `resolve_export` cleanup — DONE
### B2. Parse non-Func aliases — DONE
### B3. Implement `build_synthetic_instance` — DONE

---

## Track C: Refactoring — DONE

### C5. Double `impl Store` block — DONE
### C7. Function extraction — DONE
### C8. Panicky code → Result — DONE
### C9. Module restructuring — DONE
- [x] `decode_op`, `decode_block_type`, `peephole_optimize` moved to `instruction.rs`
- [x] `Op`, `OP_*` constants, `compile_body` extracted to new `opcode.rs`
- [x] Clean separation: `instruction.rs` = parsed IR, `opcode.rs` = compiled bytecode
### C10. Canonical ABI extraction — DONE
- [x] `lift_results`, `lift_value`, `lift_string_result` → `canonical_abi.rs`
- [x] `lower_component_args`, `lower_list` → `canonical_abi.rs`
- [x] `invoke` delegates to `invoke_component` (no code duplication)

### Low-priority refactoring (deferred)
- C1: Section parser boilerplate extraction
- C2: `CoreExport` → single struct with `kind: ExportKind` field
- C3: `From` impls for type conversions
- C4: Inconsistent error message formats
- C6: `result_types` allocation in `exec::call`

---

## Track D: Major Features

### D1. Real `make_trampoline` (cross-instance function calls)
- Current stub returns `Box::new(|_args, _mem| Vec::new())` — no-op
- Needs `Arc<Mutex<Store>>` interior mutability refactor (NOT Rc<RefCell> — must be Send+Sync)
- Trampoline closure captures shared ref to source instance store + Module clone
- Change `ComponentInstance::invoke` to borrow via `Mutex::lock`
- High complexity, high impact — unlocks all cross-instance calls
- Unlocks: comp_wt_fused (9 sub-failures), prerequisite for D2/D3

### D2. `canon lower` support
- `parse_canonical_section` only handles `CanonicalFunction::Lift`, drops `Lower`
- Without Lower, cross-component function calls (adapter pattern) fail
- Depends on D1 (real trampolines)
- Unlocks: fused, adapter, aliasing tests

### D3. String canonical ABI — DONE
- [x] Lift strings from linear memory via `(ptr, len)` pairs
- [x] `lift_string_result`, `read_string_descriptor`, `read_utf8_string` in `canonical_abi.rs`
- [x] comp_val_strings, comp_wt_strings now pass

### D3b. List canonical ABI lowering — DONE
- [x] `lower_list` calls realloc, validates pointer bounds
- [x] `lower_component_args` dispatches scalar vs list args
- [x] comp_wt_adapter now passes

### D4. `ComponentFuncTypeDef` params + arg lowering — PARTIALLY DONE
- [x] `convert_wast_args` handles Bool, S8/U8, S16/U16, Char types
- [ ] Currently only stores `result`, not params in `ComponentFuncTypeDef`

### D5. `catch_unwind` removal — PARTIALLY DONE
- [x] `Value::default_for` no longer panics (returns Result)
- [ ] Propagate Result through `Store::new_with_imports` → `ComponentInstance::instantiate`
- [ ] Remove `catch_unwind` from test harness (once no more panics possible during instantiation)

### D6. Component-level import type checking
- assert_unlinkable tests require checking that provided instances match declared import types
- Export kind matching (expected func found global, etc.)
- Export/import signature matching (function types, table types, memory limits, global types)
- Missing export detection
- Resource type matching
- Unlocks: comp_wt_modules (24 sub-failures), comp_wt_linking (4), comp_wt_instance (6), comp_wt_resources (3), comp_wt_import (1)

---

## Test Status

**Core spec tests:** 84 pass, 0 fail, 13 ignored
**Component tests:** 72 pass, 0 fail, 0 ignored

### Previously failing (now fixed):
- `comp_wt_adapter` — fixed by implementing list canonical ABI lowering (D3b)
- `comp_val_strings` — fixed by implementing string canonical ABI lifting (D3)
- `comp_async_trap_if_block_and_sync` — disabled (wast parser v245 doesn't support `thread.yield-to`)

### Test harness honesty (Track A):
- [x] `AssertTrap(Wat)` encode errors now count as failures, not passes
- [x] `Module` directive instantiation failures now count as skips, not passes
- [x] `ModuleInstance` instantiation failures now count as skips, not passes
- [x] Better error messages: `assert_return` shows both got and expected values
- [x] `convert_wast_args` handles Bool, S8/U8, S16/U16, Char types
- [x] `component_value_matches` handles F32/F64 (bit-exact comparison)

### Plasma integration
- `cargo run -p wust --example plasma_hello --release` — runs JS inside WASM, both "hello world" and fibonacci pass
- getrandom custom backend via `.cargo/config.toml` rustflags
  - TODO: patch boa fork (`AlbertMarashi/boa`, `albert/combined-fixes`) to use
    `rand = { default-features = false, features = ["small_rng"] }` and store
    a seeded `SmallRng` in boa's `Context` for `Math.random()`. Then remove
    `.cargo/config.toml` and custom getrandom backend from plasma.
- WIT interface defined at `crates/plasma/wit/world.wit`
- `make plasma-component` wraps core module as component via `wasm-tools`
