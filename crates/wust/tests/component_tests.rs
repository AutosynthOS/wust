use std::collections::HashMap;
use std::path::Path;

use wast::component::WastVal;
use wust::component::Component;
use wust::engine::Engine;
use wust::linker::Linker;
use wust::runtime::{
    ComponentArg, ComponentImportKind, ComponentInstance, ComponentValue, Value,
};

// ---------------------------------------------------------------------------
// Test runner
// ---------------------------------------------------------------------------

/// Minimal wast test runner for the component model.
///
/// Walks directives sequentially: define components, instantiate them,
/// invoke functions, check results. Tracks named definitions and
/// instances across directives.
struct WastRunner {
    /// Shared engine for parsing and validation.
    engine: Engine,
    /// Named component binaries (from `component definition`).
    definitions: HashMap<String, Vec<u8>>,
    /// All instantiated component instances.
    instances: Vec<ComponentInstance>,
    /// Maps instance names to indices in `instances`.
    named: HashMap<String, usize>,
    /// Resolves component imports during instantiation.
    linker: Linker,
    /// Index of the most recently instantiated instance.
    current: Option<usize>,
}

impl WastRunner {
    fn new() -> Self {
        let mut runner = WastRunner {
            engine: Engine::new(),
            definitions: HashMap::new(),
            instances: Vec::new(),
            named: HashMap::new(),
            linker: Linker::new(),
            current: None,
        };
        // Pre-register host builtins expected by the wasmtime test suite.
        runner.register_host(
            "host-return-two",
            ComponentImportKind::Func,
            r#"(component
            (core module $m (func (export "host-return-two") (result i32) i32.const 2))
            (core instance $m (instantiate $m))
            (func (export "host-return-two") (result u32)
                (canon lift (core func $m "host-return-two")))
        )"#,
        );
        runner
    }

    /// Parse WAT, instantiate it, and register under a name.
    fn register_host(&mut self, name: &str, kind: ComponentImportKind, wat: &str) {
        let binary = wat::parse_str(wat).expect("bad host WAT");
        let component = Component::new(&mut self.engine, &binary).expect("bad host component");
        if let Ok(instance) = component.instantiate() {
            match kind {
                ComponentImportKind::Instance => self.linker.instance(name, instance.export_view()),
                ComponentImportKind::Func => self.linker.func(name, instance.export_view()),
                _ => {}
            }
        }
    }

    /// Parse + instantiate a component binary, returning its instance index.
    fn instantiate(&mut self, binary: &[u8]) -> Result<usize, String> {
        let component = Component::new(&mut self.engine, binary)?;
        // Auto-register host shims for instance imports we can satisfy.
        for import in component.imports() {
            if import.kind == ComponentImportKind::Instance
                && !self.linker.has(&import.name)
                && !import.required_exports.is_empty()
            {
                if let Some(host) = self.build_host_for(&import.required_exports) {
                    self.linker.instance(&import.name, host.export_view());
                }
            }
        }
        let instance = self.linker.instantiate(&component)?;
        let idx = self.instances.len();
        self.instances.push(instance);
        self.current = Some(idx);
        Ok(idx)
    }

    /// Build a host instance that satisfies the given required exports.
    fn build_host_for(&self, required: &[String]) -> Option<ComponentInstance> {
        // Known host function return values.
        let known: &[(&str, u32)] = &[("return-two", 2), ("return-three", 3), ("return-four", 4)];

        // Special case: nested instance export.
        if required == ["nested"] {
            return instantiate_wat(
                r#"(component
                (core module $m (func (export "return-four") (result i32) i32.const 4))
                (core instance $m (instantiate $m))
                (func $f (result u32) (canon lift (core func $m "return-four")))
                (instance $nested (export "return-four" (func $f)))
                (export "nested" (instance $nested))
            )"#,
            );
        }

        // Special case: module export.
        if required == ["simple-module"] {
            return instantiate_wat(
                r#"(component
                (core module $m
                    (func (export "f") (result i32) i32.const 101)
                    (global (export "g") i32 i32.const 100))
                (export "simple-module" (core module $m))
            )"#,
            );
        }

        // General case: build a component exporting the required functions.
        let mut funcs = String::new();
        let mut lifts = String::new();
        for name in required {
            let val = known.iter().find(|(n, _)| *n == name)?.1;
            funcs.push_str(&format!(
                "(func (export \"{name}\") (result i32) i32.const {val})\n"
            ));
            lifts.push_str(&format!(
                "(func (export \"{name}\") (result u32) (canon lift (core func $m \"{name}\")))\n"
            ));
        }
        let wat = format!(
            "(component\n(core module $m {funcs})\n(core instance $m (instantiate $m))\n{lifts})"
        );
        instantiate_wat(&wat)
    }

    /// Look up an instance by optional name, falling back to current.
    fn get_instance(&mut self, name: Option<&str>) -> Result<&mut ComponentInstance, String> {
        let idx = match name {
            Some(n) => *self
                .named
                .get(n)
                .ok_or_else(|| format!("instance '{n}' not found"))?,
            None => self.current.ok_or("no current instance")?,
        };
        self.instances
            .get_mut(idx)
            .ok_or_else(|| format!("instance {idx} out of bounds"))
    }

    /// Invoke a named function on an instance.
    fn invoke(
        &mut self,
        func: &str,
        args: &[&WastVal],
        on: Option<&str>,
    ) -> Result<Vec<ComponentValue>, String> {
        let instance = self.get_instance(on)?;
        instance.invoke_component(func, &convert_args(args))
    }
}

// ---------------------------------------------------------------------------
// Directive execution
// ---------------------------------------------------------------------------

/// Run all directives in a .wast file, collecting errors.
fn run_wast(path: &Path) -> Vec<String> {
    let source = std::fs::read_to_string(path).unwrap();
    let source: String = source
        .lines()
        .filter(|l| !l.trim_start().starts_with(";; RUN:"))
        .collect::<Vec<_>>()
        .join("\n");

    let buf = wast::parser::ParseBuffer::new(&source).unwrap();
    let wast = wast::parser::parse::<wast::Wast>(&buf).unwrap();

    let mut runner = WastRunner::new();
    let mut errors = Vec::new();

    for (i, directive) in wast.directives.into_iter().enumerate() {
        if let Err(e) = run_directive(&mut runner, directive) {
            errors.push(format!("directive {}: {e}", i + 1));
        }
    }

    errors
}

/// Execute a single wast directive.
fn run_directive(runner: &mut WastRunner, directive: wast::WastDirective) -> Result<(), String> {
    use wast::WastDirective::*;
    use wast::WastExecute;

    match directive {
        // (component ...) — encode, instantiate, optionally name it.
        // Instantiation may fail if imports can't be resolved; that's
        // fine — the instance just won't be available for later use.
        Module(mut wat) => {
            let name = wat.name().map(|id| id.name().to_string());
            let binary = wat.encode().map_err(|e| format!("encode: {e}"))?;
            if let Some(ref n) = name {
                runner.definitions.insert(n.clone(), binary.clone());
            }
            if let Ok(idx) = runner.instantiate(&binary) {
                if let Some(n) = name {
                    let inst = runner.instances[idx].export_view();
                    runner.linker.instance(&n, inst);
                    runner.named.insert(n, idx);
                }
            }
            Ok(())
        }

        // (component definition ...) — encode and store, don't instantiate.
        ModuleDefinition(mut wat) => {
            let name = wat.name().map(|id| id.name().to_string());
            let binary = wat.encode().map_err(|e| format!("encode: {e}"))?;
            if let Some(n) = name {
                runner.definitions.insert(n, binary);
            }
            Ok(())
        }

        // (component instance $name $def) — instantiate a named definition.
        ModuleInstance {
            instance, module, ..
        } => {
            let def_name = module.map(|id| id.name().to_string());
            let binary = def_name
                .as_ref()
                .and_then(|n| runner.definitions.get(n).cloned())
                .ok_or("definition not found")?;
            let idx = runner.instantiate(&binary)?;
            if let Some(id) = instance {
                let n = id.name().to_string();
                let inst = runner.instances[idx].export_view();
                runner.linker.instance(&n, inst);
                runner.named.insert(n, idx);
            }
            Ok(())
        }

        // (register "name") — register current instance under a name.
        Register { name, module, .. } => {
            let idx = module
                .and_then(|id| runner.named.get(id.name()).copied())
                .or(runner.current)
                .ok_or("no instance to register")?;
            runner.named.insert(name.to_string(), idx);
            Ok(())
        }

        // (assert_return (invoke "f" ...) ...)
        AssertReturn {
            exec: WastExecute::Invoke(invoke),
            results,
            ..
        } => {
            let args = extract_args(&invoke);
            let on = invoke.module.map(|id| id.name());
            let got = runner.invoke(invoke.name, &args, on)?;
            if !check_results(&got, &results) {
                return Err(format!(
                    "assert_return {}(): got {got:?}, expected {}",
                    invoke.name,
                    format_expected(&results),
                ));
            }
            Ok(())
        }

        // (assert_return (component ...)) — instantiation should succeed.
        AssertReturn {
            exec: WastExecute::Wat(mut wat),
            ..
        } => {
            let binary = wat.encode().map_err(|e| format!("encode: {e}"))?;
            runner.instantiate(&binary)?;
            Ok(())
        }

        // (assert_return (get ...)) — not implemented.
        AssertReturn {
            exec: WastExecute::Get { .. },
            ..
        } => Err("assert_return(get) not implemented".into()),

        // (assert_trap (invoke "f") "msg") — invocation should fail.
        AssertTrap {
            exec: WastExecute::Invoke(invoke),
            message,
            ..
        } => {
            let args = extract_args(&invoke);
            let on = invoke.module.map(|id| id.name());
            match runner.invoke(invoke.name, &args, on) {
                Err(_) => Ok(()),
                Ok(v) => Err(format!(
                    "assert_trap {}(): should have trapped ({message}), got {v:?}",
                    invoke.name
                )),
            }
        }

        // (assert_trap (component ...)) — instantiation should fail.
        AssertTrap {
            exec: WastExecute::Wat(mut wat),
            message,
            ..
        } => {
            let binary = wat.encode().map_err(|e| format!("encode: {e}"))?;
            match runner.instantiate(&binary) {
                Err(_) => Ok(()),
                Ok(_) => Err(format!("assert_trap(wat): should have trapped ({message})")),
            }
        }

        // (assert_invalid ...) — validation should reject.
        AssertInvalid {
            mut module,
            message,
            ..
        } => match module.encode() {
            Err(_) => Ok(()),
            Ok(binary) => match Component::new(&mut runner.engine, &binary) {
                Err(_) => Ok(()),
                Ok(_) => Err(format!("assert_invalid: should have rejected ({message})")),
            },
        },

        // (assert_malformed ...) — parsing should reject.
        AssertMalformed {
            mut module,
            message,
            ..
        } => match module.encode() {
            Err(_) => Ok(()),
            Ok(binary) => match Component::new(&mut runner.engine, &binary) {
                Err(_) => Ok(()),
                Ok(_) => Err(format!(
                    "assert_malformed: should have rejected ({message})"
                )),
            },
        },

        // (assert_unlinkable ...) — linking should fail.
        AssertUnlinkable {
            mut module,
            message,
            ..
        } => match module.encode() {
            Err(_) => Ok(()),
            Ok(binary) => match runner.instantiate(&binary) {
                Err(_) => Ok(()),
                Ok(_) => Err(format!("assert_unlinkable: should have failed ({message})")),
            },
        },

        // Bare invoke.
        Invoke(invoke) => {
            let args = extract_args(&invoke);
            let on = invoke.module.map(|id| id.name());
            runner.invoke(invoke.name, &args, on)?;
            Ok(())
        }

        // Directives we don't support yet.
        AssertExhaustion { .. } => Err("assert_exhaustion not implemented".into()),
        AssertException { .. } => Err("assert_exception not implemented".into()),
        AssertSuspension { .. } => Err("assert_suspension not implemented".into()),

        _ => Err("unhandled directive".into()),
    }
}

// ---------------------------------------------------------------------------
// Value conversion helpers
// ---------------------------------------------------------------------------

/// Parse WAT and instantiate it in one shot.
fn instantiate_wat(wat: &str) -> Option<ComponentInstance> {
    let mut engine = Engine::new();
    let binary = wat::parse_str(wat).ok()?;
    let component = Component::new(&mut engine, &binary).ok()?;
    component.instantiate().ok()
}

/// Extract invoke arguments as WastVal references.
fn extract_args<'a>(invoke: &'a wast::WastInvoke<'a>) -> Vec<&'a WastVal<'a>> {
    invoke
        .args
        .iter()
        .filter_map(|a| match a {
            wast::WastArg::Component(v) => Some(v),
            _ => None,
        })
        .collect()
}

/// Convert wast values to component args.
fn convert_args(args: &[&WastVal]) -> Vec<ComponentArg> {
    args.iter().filter_map(|a| convert_arg(a)).collect()
}

/// Convert a single wast value to a component arg.
fn convert_arg(val: &WastVal) -> Option<ComponentArg> {
    Some(match val {
        WastVal::Bool(v) => ComponentArg::Value(Value::I32(if *v { 1 } else { 0 })),
        WastVal::S8(v) => ComponentArg::Value(Value::I32(*v as i32)),
        WastVal::U8(v) => ComponentArg::Value(Value::I32(*v as i32)),
        WastVal::S16(v) => ComponentArg::Value(Value::I32(*v as i32)),
        WastVal::U16(v) => ComponentArg::Value(Value::I32(*v as i32)),
        WastVal::S32(v) => ComponentArg::Value(Value::I32(*v)),
        WastVal::U32(v) => ComponentArg::Value(Value::I32(*v as i32)),
        WastVal::S64(v) => ComponentArg::Value(Value::I64(*v)),
        WastVal::U64(v) => ComponentArg::Value(Value::I64(*v as i64)),
        WastVal::F32(v) => ComponentArg::Value(Value::F32(f32::from_bits(v.bits))),
        WastVal::F64(v) => ComponentArg::Value(Value::F64(f64::from_bits(v.bits))),
        WastVal::Char(c) => ComponentArg::Value(Value::I32(*c as i32)),
        WastVal::List(items) => {
            ComponentArg::List(items.iter().filter_map(|i| convert_arg(i)).collect())
        }
        _ => unimplemented!(),
    })
}

/// Check if actual results match expected results.
fn check_results(got: &[ComponentValue], expected: &[wast::WastRet]) -> bool {
    got.len() == expected.len()
        && got.iter().zip(expected).all(|(g, e)| match e {
            wast::WastRet::Component(v) => value_matches(g, v),
            _ => false,
        })
}

/// Check if a component value matches an expected wast value.
fn value_matches(got: &ComponentValue, expected: &WastVal) -> bool {
    match (got, expected) {
        (ComponentValue::Bool(a), WastVal::Bool(b)) => a == b,
        (ComponentValue::S8(a), WastVal::S8(b)) => *a == *b as i32,
        (ComponentValue::U8(a), WastVal::U8(b)) => *a == *b as u32,
        (ComponentValue::S16(a), WastVal::S16(b)) => *a == *b as i32,
        (ComponentValue::U16(a), WastVal::U16(b)) => *a == *b as u32,
        (ComponentValue::S32(a), WastVal::S32(b)) => a == b,
        (ComponentValue::S32(a), WastVal::S8(b)) => *a == *b as i32,
        (ComponentValue::S32(a), WastVal::S16(b)) => *a == *b as i32,
        (ComponentValue::U32(a), WastVal::U32(b)) => a == b,
        (ComponentValue::U32(a), WastVal::U8(b)) => *a == *b as u32,
        (ComponentValue::U32(a), WastVal::U16(b)) => *a == *b as u32,
        (ComponentValue::S64(a), WastVal::S64(b)) => a == b,
        (ComponentValue::U64(a), WastVal::U64(b)) => a == b,
        (ComponentValue::F32(a), WastVal::F32(b)) => a.to_bits() == b.bits,
        (ComponentValue::F64(a), WastVal::F64(b)) => a.to_bits() == b.bits,
        (ComponentValue::Char(a), WastVal::Char(b)) => a == b,
        (ComponentValue::String(a), WastVal::String(b)) => a.as_str() == *b,
        _ => false,
    }
}

/// Format expected results for error messages.
fn format_expected(expected: &[wast::WastRet]) -> String {
    let parts: Vec<String> = expected
        .iter()
        .map(|e| match e {
            wast::WastRet::Component(v) => format!("{v:?}"),
            wast::WastRet::Core(v) => format!("Core({v:?})"),
            _ => "?".to_string(),
        })
        .collect();
    format!("[{}]", parts.join(", "))
}

// ---------------------------------------------------------------------------
// Test harness
// ---------------------------------------------------------------------------

fn run_component_test(name: &str, subdir: &str) {
    let path = Path::new("tests/component-model/test")
        .join(subdir)
        .join(format!("{name}.wast"));
    assert!(path.exists(), "test not found: {}", path.display());

    let errors = run_wast(&path);
    for e in &errors {
        eprintln!("  FAIL {e}");
    }
    assert!(
        errors.is_empty(),
        "{name}: {} directives failed",
        errors.len()
    );
}

macro_rules! component_tests {
    ($($name:ident => ($subdir:expr, $file:expr)),* $(,)?) => {
        $(
            #[test]
            fn $name() { run_component_test($file, $subdir); }
        )*
    };
}

component_tests! {
    // wasm-tools (parsing/validation)
    comp_empty => ("wasm-tools", "empty"),
    comp_adapt => ("wasm-tools", "adapt"),
    comp_alias => ("wasm-tools", "alias"),
    comp_big => ("wasm-tools", "big"),
    comp_definedtypes => ("wasm-tools", "definedtypes"),
    comp_example => ("wasm-tools", "example"),
    comp_export_ascription => ("wasm-tools", "export-ascription"),
    comp_export_introduces_alias => ("wasm-tools", "export-introduces-alias"),
    comp_export => ("wasm-tools", "export"),
    comp_func => ("wasm-tools", "func"),
    comp_import => ("wasm-tools", "import"),
    comp_imports_exports => ("wasm-tools", "imports-exports"),
    comp_inline_exports => ("wasm-tools", "inline-exports"),
    comp_instance_type => ("wasm-tools", "instance-type"),
    comp_instantiate => ("wasm-tools", "instantiate"),
    comp_invalid => ("wasm-tools", "invalid"),
    comp_link => ("wasm-tools", "link"),
    comp_lots_of_aliases => ("wasm-tools", "lots-of-aliases"),
    comp_lower => ("wasm-tools", "lower"),
    comp_memory64 => ("wasm-tools", "memory64"),
    comp_module_link => ("wasm-tools", "module-link"),
    comp_more_flags => ("wasm-tools", "more-flags"),
    comp_naming => ("wasm-tools", "naming"),
    comp_nested_modules => ("wasm-tools", "nested-modules"),
    comp_resources => ("wasm-tools", "resources"),
    comp_tags => ("wasm-tools", "tags"),
    comp_type_export_restrictions => ("wasm-tools", "type-export-restrictions"),
    comp_types => ("wasm-tools", "types"),
    comp_very_nested => ("wasm-tools", "very-nested"),
    comp_virtualize => ("wasm-tools", "virtualize"),
    comp_wrong_order => ("wasm-tools", "wrong-order"),

    // wasmtime (runtime behavior)
    comp_wt_adapter => ("wasmtime", "adapter"),
    comp_wt_aliasing => ("wasmtime", "aliasing"),
    comp_wt_fused => ("wasmtime", "fused"),
    comp_wt_import => ("wasmtime", "import"),
    comp_wt_instance => ("wasmtime", "instance"),
    comp_wt_linking => ("wasmtime", "linking"),
    comp_wt_modules => ("wasmtime", "modules"),
    comp_wt_nested => ("wasmtime", "nested"),
    comp_wt_resources => ("wasmtime", "resources"),
    comp_wt_restrictions => ("wasmtime", "restrictions"),
    comp_wt_simple => ("wasmtime", "simple"),
    comp_wt_strings => ("wasmtime", "strings"),
    comp_wt_tags => ("wasmtime", "tags"),
    comp_wt_types => ("wasmtime", "types"),

    // values (canonical ABI)
    comp_val_strings => ("values", "strings"),
    comp_val_trap_in_post_return => ("values", "trap-in-post-return"),

    // names
    comp_names_kebab => ("names", "kebab"),

    // resources
    comp_res_multiple => ("resources", "multiple-resources"),

    // async
    comp_async_calls_sync => ("async", "async-calls-sync"),
    comp_async_cancel_stream => ("async", "cancel-stream"),
    comp_async_cancel_subtask => ("async", "cancel-subtask"),
    comp_async_cancellable => ("async", "cancellable"),
    comp_async_closed_stream => ("async", "closed-stream"),
    comp_async_cross_abi_calls => ("async", "cross-abi-calls"),
    comp_async_deadlock => ("async", "deadlock"),
    comp_async_dont_block_start => ("async", "dont-block-start"),
    comp_async_drop_cross_task_borrow => ("async", "drop-cross-task-borrow"),
    comp_async_drop_stream => ("async", "drop-stream"),
    comp_async_drop_subtask => ("async", "drop-subtask"),
    comp_async_drop_waitable_set => ("async", "drop-waitable-set"),
    comp_async_empty_wait => ("async", "empty-wait"),
    comp_async_futures_must_write => ("async", "futures-must-write"),
    comp_async_partial_stream_copies => ("async", "partial-stream-copies"),
    comp_async_passing_resources => ("async", "passing-resources"),
    comp_async_same_component_stream_future => ("async", "same-component-stream-future"),
    comp_async_sync_barges_in => ("async", "sync-barges-in"),
    comp_async_sync_streams => ("async", "sync-streams"),
    comp_async_trap_if_done => ("async", "trap-if-done"),
    comp_async_trap_on_reenter => ("async", "trap-on-reenter"),
    comp_async_wait_during_callback => ("async", "wait-during-callback"),
    comp_async_zero_length => ("async", "zero-length"),
}
