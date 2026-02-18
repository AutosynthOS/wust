# Component Model Runtime — TODO

## Track A: Test Harness Honesty + Coverage

### A1. Tighten assertion handlers — DONE
- [x] `AssertInvalid` that passes validation -> **fail**, not skip
- [x] `AssertUnlinkable` that instantiates successfully -> **fail**, not skip
- [x] `AssertMalformed` that parses successfully -> **fail**, not skip
- [ ] `AssertTrap(Wat)` encode errors should not count as passes (conflates harness issues with traps)
- [ ] `Module` directive `Ok(()) | Err(_) => passed` masks instantiation regressions

### A2. Named definition + instance registry
- Add `definitions: HashMap<String, Vec<u8>>` to `ComponentTestRunner`
- Add `named_instances: HashMap<String, ComponentInstance>`
- `ModuleDefinition`: encode, extract `QuoteWat::name()`, store in definitions
- `ModuleInstance { instance, module }`: look up module in definitions, instantiate, store as instance name
- `Module` (bare component): also extract name and store in both maps
- Update `invoke_component` to support `WastInvoke.module` for named instance dispatch
- Unlocks directives in: modules, nested, aliasing, linking tests

---

## Track B: Runtime Correctness — DONE

### B1. `resolve_export` cleanup — DONE
- [x] Remove leaky `self_idx` parameter from `CoreInstance::resolve_export`
- [x] Return `Option<(ExportKind, u32)>` instead of `Option<CoreExport>`
- [x] Added `ComponentInstance::resolve_core_export` for callers that need full `CoreExport`
- [x] Added `make_core_export` helper

### B2. Parse non-Func aliases — DONE
- [x] Added `CoreGlobalDef`, `CoreMemoryDef`, `CoreTableDef` enums
- [x] Added `core_globals`, `core_memories`, `core_tables` fields to `Component`
- [x] `parse_alias_section` handles all 4 external kinds
- [x] `AliasInstanceExportDef` trait + macro to DRY up the 4 alias types

### B3. Implement `build_synthetic_instance` — DONE
- [x] `resolve_alias_to_core_export` resolves any alias kind to a live `CoreExport`
- [x] `resolve_aliased_export` provides descriptive error messages
- [x] `get_alias_coords` generic function collapsed 4 identical match arms

---

## Track C: Refactoring — MOSTLY DONE

### C1. Section parser boilerplate
- All 5 `parse_*_section` functions share identical `for item in reader { let item = item.map_err(...)? }` pattern
- Could extract a generic `parse_section(reader, closure)` helper
- Low priority — pattern is simple and explicit

### C2. `CoreExport` simplification
- All 4 variants carry identical `{ instance, index }` fields
- Could collapse into a single struct with a `kind: ExportKind` field
- Low priority — current form is clear

### C3. `From` impls for type conversions
- `ComponentExternalKind` from `wasmparser::ComponentExternalKind` (6-arm match -> From impl)
- `ComponentResultType` from `wasmparser::PrimitiveValType` (13-arm match -> From impl)

### C4. Inconsistent error messages
- Section parsers use varying formats: "instance parse error", "alias parse error", etc.
- Should follow consistent template like "failed to parse {section} section: {e}"

### C5. Double `impl Store` block — DONE
- [x] Merged into single `impl Store` block

### C6. `result_types` allocation in `exec::call`
- `.to_vec()` on every call could be avoided by storing as reference

### C7. Function extraction — DONE
- [x] `component.rs`: extracted `resolve_single_import`, `find_arg_instance`, `provide_default_import`, `register_core_instance_export`, `resolve_single_export`, `lookup_result_type`, `resolve_core_func_export`
- [x] `exec.rs`: extracted `execute_table_init`, `execute_memory_init`, `execute_table_copy`, `resolve_table_element`, `check_indirect_type`, `coerce_bits_to_global`
- [x] `module.rs`: `ModuleBuilder` pattern, `from_bytes` now 8 lines, extracted 7 section-handling methods + 4 free functions

### C8. Panicky code → Result — DONE
- [x] `Value::default_for` returns `Result<Self, String>` instead of panicking with `todo!()`
- [x] `exec.rs`: converted 6 direct-index panics to proper `Result` returns (`new_frame`, `call`, `OP_GLOBAL_GET`, `OP_GLOBAL_SET`, `OP_CALL`, `OP_CALL_INDIRECT`)
- [x] Left validation-guaranteed `.unwrap()` calls in hot paths (safe by WASM validation invariants)

### C9. Module restructuring — TODO
- [ ] Split `instruction.rs`: extract `Op`, `OP_*` constants, `compile_body()` into new `opcode.rs`
- [ ] Move `decode_op` from `module.rs` → `instruction.rs` (it produces `Instruction` values)
- [ ] Move `peephole_optimize` from `module.rs` → `instruction.rs` (superinstruction fuser belongs with superinstruction definitions)
- [ ] Extract `ComponentResultType` + canonical ABI lifting into `canonical.rs`
- [ ] Tighten visibility: `OP_*` constants, `Instruction`, `Op` → `pub(crate)`
- [ ] Move `eval_const_expr`, `resolve_elem_item` from `store.rs` → `module.rs`

---

## Track D: Major Features (deferred)

### D1. Real `make_trampoline` (cross-instance function calls)
- Current stub returns `Box::new(|_args, _mem| Vec::new())` — no-op
- Needs `Arc<Mutex<Store>>` interior mutability refactor (NOT Rc<RefCell> — must be Send+Sync)
- Trampoline closure captures shared ref to source instance store + Module clone
- Change `ComponentInstance::invoke` to borrow via `Mutex::lock`
- High complexity, high impact — unlocks all cross-instance calls

### D2. `canon lower` support
- `parse_canonical_section` only handles `CanonicalFunction::Lift`, drops `Lower`
- Without Lower, cross-component function calls (adapter pattern) fail
- Depends on D1 (real trampolines)
- Unlocks: fused, adapter, aliasing tests

### D3. String canonical ABI
- Lift strings from linear memory via `(ptr, len)` pairs
- `ComponentValue::String` exists but is never constructed by `lift_value`
- Requires reading from target instance's `Store::memory`
- Depends on D1 (make_trampoline for cross-instance string passing)
- Unlocks: comp_val_strings, comp_wt_strings

### D4. `ComponentFuncTypeDef` params + arg lowering
- Currently only stores `result`, not params
- `convert_wast_args` drops Bool/S8/U8/S16/U16/Char/String (returns None)
- Add params to `ComponentFuncTypeDef`, extend `convert_wast_args`

### D5. `catch_unwind` removal — PARTIALLY DONE
- [x] `Value::default_for` no longer panics (returns Result)
- [ ] Propagate Result through `Store::new_with_imports` → `ComponentInstance::instantiate`
- [ ] Remove `catch_unwind` from test harness (once no more panics possible during instantiation)

---

## Test Status

**Core spec tests:** 84 pass, 0 fail, 13 ignored
**Component tests:** 59 pass, 14 fail, 0 ignored

### Failing component tests (all pre-existing, represent real gaps):
- `comp_wt_simple` (2 failures) — wasmtime-specific validation rules not in wasmparser
- `comp_wt_import` (2 failures) — import type mismatch checking not implemented
- `comp_wt_types` — component type checking gaps
- `comp_wt_restrictions` — component restrictions not enforced
- `comp_wt_fused` (9 failures) — cross-instance calls (needs D1 make_trampoline)
- `comp_wt_adapter` — adapter pattern (needs D1 + D2)
- `comp_wt_strings` — string canonical ABI (needs D3)
- `comp_val_strings` — string canonical ABI (needs D3)
- `comp_wt_instance` — assert_unlinkable gaps
- `comp_wt_linking` — assert_unlinkable gaps
- `comp_wt_modules` — assert_unlinkable gaps
- `comp_wt_resources` — assert_unlinkable gaps
- `comp_async_dont_block_start` — async component model
- `comp_async_trap_if_block_and_sync` — async component model

### Plasma integration
- `cargo run -p wust --example plasma_hello --release` — runs JS inside WASM, both "hello world" and fibonacci pass
- `getrandom/wasm_js` dependency works for now (dead-code eliminated), will need `custom` feature when `Math.random()` is used
