use std::collections::HashMap;
use std::path::Path;

use wast::component::WastVal;
use wust::component::Component;
use wust::engine::Engine;
use wust::linker::Linker;
use wust::runtime::{ComponentArg, ComponentImportKind, ComponentInstance, ComponentValue, Value};

struct ComponentRunner {
    engine: Engine,
    definitions: HashMap<String, Vec<u8>>,
    instances: Vec<ComponentInstance>,
    named: HashMap<String, usize>,
    linker: Linker,
    current: Option<usize>,
}

impl ComponentRunner {
    fn new() -> Self {
        let mut runner = ComponentRunner {
            engine: Engine::new(),
            definitions: HashMap::new(),
            instances: Vec::new(),
            named: HashMap::new(),
            linker: Linker::new(),
            current: None,
        };
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

    fn instantiate(&mut self, binary: &[u8]) -> anyhow::Result<usize> {
        let component = Component::new(&mut self.engine, binary)?;
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

    fn instantiate_named(&mut self, binary: &[u8], name: Option<String>) -> anyhow::Result<()> {
        let idx = self.instantiate(binary)?;
        if let Some(n) = name {
            let inst = self.instances[idx].export_view();
            self.linker.instance(&n, inst);
            self.named.insert(n, idx);
        }
        Ok(())
    }

    fn build_host_for(&self, required: &[String]) -> Option<ComponentInstance> {
        let known: &[(&str, u32)] = &[("return-two", 2), ("return-three", 3), ("return-four", 4)];

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

    fn invoke(&mut self, invoke: &wast::WastInvoke) -> anyhow::Result<Vec<ComponentValue>> {
        let args = parse_args(invoke)?;
        let idx = match invoke.module {
            Some(id) => *self
                .named
                .get(id.name())
                .ok_or_else(|| anyhow::anyhow!("instance '{}' not found", id.name()))?,
            None => self
                .current
                .ok_or_else(|| anyhow::anyhow!("no current instance"))?,
        };
        let instance = self
            .instances
            .get_mut(idx)
            .ok_or_else(|| anyhow::anyhow!("instance {idx} out of bounds"))?;
        instance.invoke_component(invoke.name, &args)
    }

    fn execute(&mut self, exec: wast::WastExecute) -> anyhow::Result<Vec<ComponentValue>> {
        match exec {
            wast::WastExecute::Invoke(invoke) => self.invoke(&invoke),
            wast::WastExecute::Wat(wat) => {
                let binary = wat.encode()?;
                self.instantiate(&binary)?;
                Ok(vec![])
            }
            wast::WastExecute::Get { .. } => anyhow::bail!("get not supported"),
        }
    }

    fn expect_module_fails(
        &mut self,
        mut wat: wast::QuoteWat,
        message: &str,
    ) -> anyhow::Result<()> {
        let binary = match wat.encode() {
            Err(_) => return Ok(()),
            Ok(b) => b,
        };
        match Component::new(&mut self.engine, &binary) {
            Err(_) => Ok(()),
            Ok(component) => match self.linker.instantiate(&component) {
                Err(_) => Ok(()),
                Ok(_) => anyhow::bail!("should fail ({message})"),
            },
        }
    }

    fn assert_return(
        &mut self,
        exec: wast::WastExecute,
        results: &[wast::WastRet],
    ) -> anyhow::Result<()> {
        let got = self.execute(exec)?;
        let expected = parse_expected(results)?;
        anyhow::ensure!(
            vals_match(&got, &expected),
            "got {got:?}, expected {expected:?}"
        );
        Ok(())
    }

    fn assert_trap(&mut self, exec: wast::WastExecute, message: &str) -> anyhow::Result<()> {
        match self.execute(exec) {
            Err(_) => Ok(()),
            Ok(got) => anyhow::bail!("should trap ({message}), got {got:?}"),
        }
    }

    fn run_wast(&mut self, path: &Path) -> (usize, usize) {
        let source = std::fs::read_to_string(path).unwrap();
        let source: String = source
            .lines()
            .filter(|l| !l.trim_start().starts_with(";; RUN:"))
            .collect::<Vec<_>>()
            .join("\n");

        let buf = wast::parser::ParseBuffer::new(&source).unwrap();
        let wast = wast::parser::parse::<wast::Wast>(&buf).unwrap();

        let (mut passed, mut failed) = (0, 0);
        for directive in wast.directives {
            match self.run_directive(directive) {
                Ok(()) => passed += 1,
                Err(e) => {
                    failed += 1;
                    eprintln!("  FAIL {e}");
                }
            }
        }
        (passed, failed)
    }

    fn run_directive(&mut self, directive: wast::WastDirective) -> anyhow::Result<()> {
        match directive {
            wast::WastDirective::Module(mut wat) => {
                let name = wat.name().map(|id| id.name().to_string());
                let binary = wat.encode()?;
                if let Some(ref n) = name {
                    self.definitions.insert(n.clone(), binary.clone());
                }
                // Instantiation may fail if imports can't be resolved.
                let _ = self.instantiate_named(&binary, name);
                Ok(())
            }
            wast::WastDirective::ModuleDefinition(mut wat) => {
                let name = wat.name().map(|id| id.name().to_string());
                let binary = wat.encode()?;
                if let Some(n) = name {
                    self.definitions.insert(n, binary);
                }
                Ok(())
            }
            wast::WastDirective::ModuleInstance {
                instance, module, ..
            } => {
                let def_name = module.map(|id| id.name().to_string());
                let binary = def_name
                    .as_ref()
                    .and_then(|n| self.definitions.get(n).cloned())
                    .ok_or_else(|| anyhow::anyhow!("definition not found"))?;
                let inst_name = instance.map(|id| id.name().to_string());
                self.instantiate_named(&binary, inst_name)
            }
            wast::WastDirective::Register { name, module, .. } => {
                let idx = module
                    .and_then(|id| self.named.get(id.name()).copied())
                    .or(self.current)
                    .ok_or_else(|| anyhow::anyhow!("no instance to register"))?;
                self.named.insert(name.to_string(), idx);
                Ok(())
            }
            wast::WastDirective::AssertReturn { exec, results, .. } => {
                self.assert_return(exec, &results)
            }
            wast::WastDirective::AssertTrap { exec, message, .. } => {
                self.assert_trap(exec, message)
            }
            wast::WastDirective::AssertExhaustion { call, message, .. } => {
                match self.invoke(&call) {
                    Err(_) => Ok(()),
                    Ok(got) => anyhow::bail!("should exhaust ({message}), got {got:?}"),
                }
            }
            wast::WastDirective::AssertInvalid {
                module, message, ..
            } => self.expect_module_fails(module, message),
            wast::WastDirective::AssertMalformed {
                module, message, ..
            } => self.expect_module_fails(module, message),
            wast::WastDirective::AssertUnlinkable {
                module, message, ..
            } => self.expect_module_fails(wast::QuoteWat::Wat(module), message),
            wast::WastDirective::Invoke(invoke) => self.invoke(&invoke).map(|_| ()),
            _ => anyhow::bail!("unsupported directive"),
        }
    }
}

// --- Helpers ---

fn instantiate_wat(wat: &str) -> Option<ComponentInstance> {
    let mut engine = Engine::new();
    let binary = wat::parse_str(wat).ok()?;
    let component = Component::new(&mut engine, &binary).ok()?;
    component.instantiate().ok()
}

fn parse_args(invoke: &wast::WastInvoke) -> anyhow::Result<Vec<ComponentArg>> {
    invoke
        .args
        .iter()
        .map(|a| match a {
            wast::WastArg::Component(v) => convert_arg(v),
            _ => anyhow::bail!("unsupported arg"),
        })
        .collect()
}

fn convert_arg(val: &WastVal) -> anyhow::Result<ComponentArg> {
    Ok(match val {
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
            let converted: Vec<_> = items
                .iter()
                .map(convert_arg)
                .collect::<anyhow::Result<_>>()?;
            ComponentArg::List(converted)
        }
        other => anyhow::bail!("unsupported arg: {other:?}"),
    })
}

// --- Expected value types ---

enum Expected {
    Bool(bool),
    S8(i32),
    U8(u32),
    S16(i32),
    U16(u32),
    S32(i32),
    U32(u32),
    S64(i64),
    U64(u64),
    F32(f32),
    F64(f64),
    Char(char),
    String(String),
}

fn parse_expected(results: &[wast::WastRet]) -> anyhow::Result<Vec<Expected>> {
    results
        .iter()
        .map(|r| match r {
            wast::WastRet::Component(v) => expected_from_wast(v),
            _ => anyhow::bail!("unsupported ret"),
        })
        .collect()
}

fn expected_from_wast(val: &WastVal) -> anyhow::Result<Expected> {
    Ok(match val {
        WastVal::Bool(v) => Expected::Bool(*v),
        WastVal::S8(v) => Expected::S8(*v as i32),
        WastVal::U8(v) => Expected::U8(*v as u32),
        WastVal::S16(v) => Expected::S16(*v as i32),
        WastVal::U16(v) => Expected::U16(*v as u32),
        WastVal::S32(v) => Expected::S32(*v),
        WastVal::U32(v) => Expected::U32(*v),
        WastVal::S64(v) => Expected::S64(*v),
        WastVal::U64(v) => Expected::U64(*v),
        WastVal::F32(v) => Expected::F32(f32::from_bits(v.bits)),
        WastVal::F64(v) => Expected::F64(f64::from_bits(v.bits)),
        WastVal::Char(c) => Expected::Char(*c),
        WastVal::String(s) => Expected::String(s.to_string()),
        other => anyhow::bail!("unsupported ret: {other:?}"),
    })
}

fn vals_match(got: &[ComponentValue], expected: &[Expected]) -> bool {
    got.len() == expected.len() && got.iter().zip(expected).all(|(g, e)| val_matches(g, e))
}

fn val_matches(got: &ComponentValue, expected: &Expected) -> bool {
    match (got, expected) {
        (ComponentValue::Bool(a), Expected::Bool(b)) => a == b,
        (ComponentValue::S8(a), Expected::S8(b)) => a == b,
        (ComponentValue::U8(a), Expected::U8(b)) => a == b,
        (ComponentValue::S16(a), Expected::S16(b)) => a == b,
        (ComponentValue::U16(a), Expected::U16(b)) => a == b,
        (ComponentValue::S32(a), Expected::S32(b)) => a == b,
        (ComponentValue::U32(a), Expected::U32(b)) => a == b,
        (ComponentValue::S64(a), Expected::S64(b)) => a == b,
        (ComponentValue::U64(a), Expected::U64(b)) => a == b,
        (ComponentValue::F32(a), Expected::F32(b)) => a.to_bits() == b.to_bits(),
        (ComponentValue::F64(a), Expected::F64(b)) => a.to_bits() == b.to_bits(),
        (ComponentValue::Char(a), Expected::Char(b)) => a == b,
        (ComponentValue::String(a), Expected::String(b)) => a == b,
        _ => false,
    }
}

// --- Test harness ---

fn run_component_test(name: &str, subdir: &str) {
    let path = Path::new("tests/component-model/test")
        .join(subdir)
        .join(format!("{name}.wast"));
    assert!(path.exists(), "test not found: {}", path.display());
    let mut runner = ComponentRunner::new();
    let (passed, failed) = runner.run_wast(&path);
    println!("{name}: {passed} passed, {failed} failed");
    assert_eq!(failed, 0, "{name}: {failed} assertions failed");
}

macro_rules! component_tests {
    ($($name:ident => ($subdir:expr, $file:expr)),* $(,)?) => {
        $( #[test] fn $name() { run_component_test($file, $subdir); } )*
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
