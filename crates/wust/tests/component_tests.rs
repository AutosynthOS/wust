use std::collections::HashMap;
use std::path::Path;
use wast::WastRet;
use wast::component::WastVal;
use wust::runtime::{
    Component, ComponentArg, ComponentImportKind, ComponentInstance, ComponentValue, Value,
};

/// Component model test runner.
///
/// Tracks named component definitions and instances across directives,
/// similar to how the core spec test runner tracks modules and stores.
struct ComponentTestRunner {
    /// All instantiated component instances.
    instances: Vec<ComponentInstance>,
    /// Index of the most recently instantiated instance.
    current_instance: Option<usize>,
    /// Named component binaries (from ModuleDefinition or named Module).
    definitions: HashMap<String, Vec<u8>>,
    /// Maps instance names to indices in `instances`.
    named_instances: HashMap<String, usize>,
    /// Tracks the kind of entity registered under each name.
    named_kinds: HashMap<String, ComponentImportKind>,
}

impl ComponentTestRunner {
    fn new() -> Self {
        let mut runner = ComponentTestRunner {
            instances: Vec::new(),
            current_instance: None,
            definitions: HashMap::new(),
            named_instances: HashMap::new(),
            named_kinds: HashMap::new(),
        };
        runner.register_host_builtins();
        runner
    }

    /// Register host builtin instances expected by the wasmtime test suite.
    ///
    /// Creates real component instances with working functions so that
    /// tests importing host-provided functions can exercise the full
    /// cross-instance call path.
    fn register_host_builtins(&mut self) {
        // "host-return-two" — a func returning u32(2).
        self.register_host_func_component("host-return-two", "host-return-two", 2);
    }

    /// Register a component that exports a single function returning a
    /// constant u32 value.
    fn register_host_func_component(
        &mut self,
        name: &str,
        export_name: &str,
        return_value: u32,
    ) {
        let wat = format!(
            r#"(component
              (core module $m
                (func (export "{export_name}") (result i32) i32.const {return_value})
              )
              (core instance $m (instantiate $m))
              (func (export "{export_name}") (result u32)
                (canon lift (core func $m "{export_name}"))
              )
            )"#,
        );
        let binary = wat::parse_str(&wat).expect("failed to parse host func WAT");
        let component =
            Component::from_bytes(&binary).expect("failed to parse host func component");
        match ComponentInstance::instantiate(&component) {
            Ok(instance) => {
                let idx = self.instances.len();
                self.instances.push(instance);
                self.named_instances.insert(name.to_string(), idx);
                self.named_kinds
                    .insert(name.to_string(), ComponentImportKind::Func);
            }
            Err(e) => {
                eprintln!("  WARNING: failed to create host func '{name}': {e}");
                self.named_kinds
                    .insert(name.to_string(), ComponentImportKind::Func);
            }
        }
    }

    /// Build a host instance on the fly for a specific set of required exports.
    ///
    /// Returns a ComponentInstance that exports the given functions, each
    /// returning a constant u32 value.
    fn build_host_instance_for(
        &mut self,
        required_exports: &[String],
    ) -> Option<ComponentInstance> {
        // Map of known host function names to their return values.
        let known_funcs: HashMap<&str, u32> = [
            ("return-three", 3),
            ("return-four", 4),
            ("return-two", 2),
        ]
        .into_iter()
        .collect();

        // Check if all required exports are known functions.
        // If any required export is not a known func (e.g. "nested",
        // "simple-module", "x", type exports), we can't satisfy it
        // and should return None to let the default empty instance be used.
        let mut func_exports = Vec::new();
        for name in required_exports {
            if let Some(&val) = known_funcs.get(name.as_str()) {
                func_exports.push((name.clone(), val));
            } else {
                return None;
            }
        }

        if func_exports.is_empty() {
            return None;
        }

        // Build a component WAT with all the needed exports.
        let mut core_funcs = String::new();
        let mut lifts = String::new();
        for (name, val) in &func_exports {
            core_funcs.push_str(&format!(
                "    (func (export \"{name}\") (result i32) i32.const {val})\n"
            ));
            lifts.push_str(&format!(
                "  (func (export \"{name}\") (result u32) (canon lift (core func $m \"{name}\")))\n"
            ));
        }
        let wat = format!(
            "(component\n  (core module $m\n{core_funcs}  )\n  (core instance $m (instantiate $m))\n{lifts})"
        );
        let binary = wat::parse_str(&wat).ok()?;
        let component = Component::from_bytes(&binary).ok()?;
        ComponentInstance::instantiate(&component).ok()
    }

    /// Build a map of named imports for a component by looking up each
    /// import name in the test runner's registered instances.
    ///
    /// For instance imports whose required exports are all known host
    /// functions, dynamically builds a host instance. Otherwise, the import
    /// gets the default empty instance.
    ///
    /// Returns `Err` if a kind mismatch is detected (e.g. component expects
    /// a module but a registered instance exists under that name).
    fn resolve_component_imports(
        &mut self,
        component: &Component,
    ) -> Result<HashMap<String, ComponentInstance>, String> {
        let mut map = HashMap::new();
        for import in component.imports() {
            if let Some(registered_kind) = self.named_kinds.get(&import.name) {
                if import.kind != *registered_kind {
                    let expected = format!("{:?}", import.kind).to_lowercase();
                    let found = format!("{:?}", registered_kind).to_lowercase();
                    return Err(format!("expected {} found {}", expected, found,));
                }
            } else if !matches!(
                import.kind,
                ComponentImportKind::Instance
                    | ComponentImportKind::Type
                    | ComponentImportKind::Component
                    | ComponentImportKind::Value
            ) {
                // Func and Module imports must be registered in the test
                // environment. Instance/Type/Component/Value imports get
                // defaults when not explicitly provided.
                return Err(format!("import `{}` was not found", import.name,));
            }
            if let Some(idx) = self.named_instances.get(&import.name) {
                if let Some(instance) = self.instances.get(*idx) {
                    map.insert(import.name.clone(), instance.export_view());
                }
            } else if import.kind == ComponentImportKind::Instance
                && !import.required_exports.is_empty()
            {
                // Try to build a host instance on the fly for known func exports.
                if let Some(host_inst) =
                    self.build_host_instance_for(&import.required_exports)
                {
                    map.insert(import.name.clone(), host_inst.export_view());
                }
            }
        }
        Ok(map)
    }

    /// Try to instantiate a component binary, returning the instance index.
    ///
    /// Validates the binary, then tries to build a live `ComponentInstance`.
    /// Panics from unsupported features are caught and converted to errors.
    fn try_instantiate(&mut self, binary: &[u8]) -> Result<usize, String> {
        let component = Component::from_bytes(binary)?;
        let imports = self.resolve_component_imports(&component)?;
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            ComponentInstance::instantiate_with_imports(&component, imports)
        })) {
            Ok(Ok(instance)) => {
                let idx = self.instances.len();
                self.instances.push(instance);
                self.current_instance = Some(idx);
                Ok(idx)
            }
            Ok(Err(e)) => {
                self.current_instance = None;
                Err(e)
            }
            Err(_panic) => {
                self.current_instance = None;
                Err("panic during instantiation".into())
            }
        }
    }

    /// Invoke a named function on a component instance.
    ///
    /// Converts wast args to core values, calls `invoke` which performs
    /// canonical ABI lifting internally, and returns component values.
    fn invoke_component(
        &mut self,
        func_name: &str,
        args: &[&WastVal],
        module_name: Option<&str>,
    ) -> Result<Vec<ComponentValue>, String> {
        let idx = match module_name {
            Some(name) => *self
                .named_instances
                .get(name)
                .ok_or_else(|| format!("named instance '{}' not found", name))?,
            None => self
                .current_instance
                .ok_or_else(|| "no current component instance".to_string())?,
        };
        let instance = self
            .instances
            .get_mut(idx)
            .ok_or_else(|| format!("instance index {} out of bounds", idx))?;
        let component_args = convert_wast_args_to_component(args);
        instance.invoke_component(func_name, &component_args)
    }

    fn run_wast(&mut self, path: &Path) -> (usize, usize) {
        let source = std::fs::read_to_string(path).unwrap();
        // Strip ;; RUN: ... lines that aren't part of the wast spec
        let source: String = source
            .lines()
            .filter(|line| !line.trim_start().starts_with(";; RUN:"))
            .collect::<Vec<_>>()
            .join("\n");
        let buf = wast::parser::ParseBuffer::new(&source).unwrap();
        let wast = match wast::parser::parse::<wast::Wast>(&buf) {
            Ok(w) => w,
            Err(e) => {
                eprintln!("  PARSE ERROR: {e}");
                return (0, 1);
            }
        };

        let mut passed = 0usize;
        let mut failed = 0usize;
        let mut directive_idx = 0usize;

        for directive in wast.directives {
            directive_idx += 1;
            match directive {
                // A bare (component ...) — encode and try to instantiate.
                wast::WastDirective::Module(mut wat) => {
                    let name = wat.name().map(|id| id.name().to_string());
                    match wat.encode() {
                        Ok(binary) => {
                            if let Some(ref n) = name {
                                self.definitions.insert(n.clone(), binary.clone());
                            }
                            match self.try_instantiate(&binary) {
                                Ok(idx) => {
                                    if let Some(ref n) = name {
                                        self.named_instances.insert(n.clone(), idx);
                                        self.named_kinds
                                            .insert(n.clone(), ComponentImportKind::Instance);
                                    }
                                    passed += 1;
                                }
                                Err(e) => {
                                    failed += 1;
                                    eprintln!(
                                        "  FAIL component instantiation (directive {directive_idx}): {e}"
                                    );
                                }
                            }
                        }
                        Err(e) => {
                            self.current_instance = None;
                            failed += 1;
                            eprintln!("  FAIL encode: {e}");
                        }
                    }
                }

                // `component definition $name` — define but don't instantiate.
                wast::WastDirective::ModuleDefinition(mut wat) => {
                    let name = wat.name().map(|id| id.name().to_string());
                    match wat.encode() {
                        Ok(binary) => {
                            if let Some(n) = name {
                                self.definitions.insert(n, binary);
                            }
                            passed += 1;
                        }
                        Err(e) => {
                            failed += 1;
                            eprintln!("  FAIL encode definition: {e}");
                        }
                    }
                }

                // `component instance $name $def` — instantiate a named definition.
                wast::WastDirective::ModuleInstance {
                    instance, module, ..
                } => {
                    let module_name = module.map(|id| id.name().to_string());
                    let bytes = module_name
                        .as_ref()
                        .and_then(|n| self.definitions.get(n).cloned());
                    match bytes {
                        Some(binary) => match self.try_instantiate(&binary) {
                            Ok(idx) => {
                                if let Some(id) = instance {
                                    let n = id.name().to_string();
                                    self.named_kinds
                                        .insert(n.clone(), ComponentImportKind::Instance);
                                    self.named_instances.insert(n, idx);
                                }
                                passed += 1;
                            }
                            Err(e) => {
                                failed += 1;
                                eprintln!("  FAIL instance instantiation: {e}");
                            }
                        },
                        None => {
                            failed += 1;
                            eprintln!("  FAIL instance: definition not found");
                        }
                    }
                }

                // `register "name"` — register current instance under a name.
                wast::WastDirective::Register { name, module, .. } => {
                    let idx = module
                        .and_then(|id| self.named_instances.get(id.name()).copied())
                        .or(self.current_instance);
                    match idx {
                        Some(i) => {
                            self.named_instances.insert(name.to_string(), i);
                            self.named_kinds
                                .insert(name.to_string(), ComponentImportKind::Instance);
                            passed += 1;
                        }
                        None => {
                            failed += 1;
                            eprintln!("  FAIL register: no instance available");
                        }
                    }
                }

                // assert_return with invoke
                wast::WastDirective::AssertReturn {
                    exec: wast::WastExecute::Invoke(invoke),
                    results,
                    ..
                } => {
                    let module_name = invoke.module.map(|id| id.name());
                    let has_instance = match module_name {
                        Some(n) => self.named_instances.contains_key(n),
                        None => self.current_instance.is_some(),
                    };
                    if !has_instance {
                        failed += 1;
                        eprintln!(
                            "  FAIL assert_return {}(): no instance available",
                            invoke.name
                        );
                        continue;
                    }
                    let args = extract_component_args(&invoke);
                    match self.invoke_component(invoke.name, &args, module_name) {
                        Ok(got) => {
                            if check_results(&got, &results) {
                                passed += 1;
                            } else {
                                failed += 1;
                                eprintln!(
                                    "  FAIL assert_return {}(): got {:?}, expected {:?}",
                                    invoke.name,
                                    got,
                                    format_expected(&results),
                                );
                            }
                        }
                        Err(e) => {
                            failed += 1;
                            eprintln!("  FAIL assert_return {}(): {e}", invoke.name);
                        }
                    }
                }

                // assert_return with Wat (instantiate, check no error)
                wast::WastDirective::AssertReturn {
                    exec: wast::WastExecute::Wat(mut wat),
                    ..
                } => match wat.encode() {
                    Ok(binary) => match self.try_instantiate(&binary) {
                        Ok(_) => {
                            passed += 1;
                        }
                        Err(e) => {
                            failed += 1;
                            eprintln!("  FAIL assert_return(wat): {e}");
                        }
                    },
                    Err(e) => {
                        failed += 1;
                        eprintln!("  FAIL assert_return(wat) encode: {e}");
                    }
                },

                // assert_return with get
                wast::WastDirective::AssertReturn {
                    exec: wast::WastExecute::Get { .. },
                    ..
                } => {
                    failed += 1;
                    eprintln!("  FAIL assert_return(get): not implemented");
                }

                // assert_trap with invoke
                wast::WastDirective::AssertTrap {
                    exec: wast::WastExecute::Invoke(invoke),
                    message,
                    ..
                } => {
                    let module_name = invoke.module.map(|id| id.name());
                    let has_instance = match module_name {
                        Some(n) => self.named_instances.contains_key(n),
                        None => self.current_instance.is_some(),
                    };
                    if !has_instance {
                        failed += 1;
                        eprintln!(
                            "  FAIL assert_trap {}(): no instance available",
                            invoke.name
                        );
                        continue;
                    }
                    let args = extract_component_args(&invoke);
                    match self.invoke_component(invoke.name, &args, module_name) {
                        Err(_) => {
                            passed += 1;
                        }
                        Ok(v) => {
                            failed += 1;
                            eprintln!(
                                "  FAIL assert_trap {}(): should have trapped ({message}), got {v:?}",
                                invoke.name
                            );
                        }
                    }
                }

                // assert_trap with Wat (instantiation should trap)
                wast::WastDirective::AssertTrap {
                    exec: wast::WastExecute::Wat(mut wat),
                    message,
                    ..
                } => match wat.encode() {
                    Ok(binary) => match self.try_instantiate(&binary) {
                        Err(_) => {
                            passed += 1;
                        }
                        Ok(_) => {
                            failed += 1;
                            eprintln!("  FAIL assert_trap(wat): should have trapped ({message})");
                        }
                    },
                    Err(e) => {
                        failed += 1;
                        eprintln!(
                            "  FAIL assert_trap(wat) encode error \
                                 (harness issue, not a trap): {e}"
                        );
                    }
                },

                // assert_invalid: component should fail validation
                wast::WastDirective::AssertInvalid {
                    mut module,
                    message,
                    ..
                } => match module.encode() {
                    Ok(binary) => match Component::from_bytes(&binary) {
                        Err(_) => {
                            passed += 1;
                        }
                        Ok(_) => {
                            failed += 1;
                            eprintln!(
                                "  FAIL assert_invalid: validation should have rejected ({message})"
                            );
                        }
                    },
                    Err(_) => {
                        passed += 1;
                    }
                },

                // assert_malformed: component should fail to parse
                wast::WastDirective::AssertMalformed {
                    mut module,
                    message,
                    ..
                } => match module.encode() {
                    Ok(binary) => match Component::from_bytes(&binary) {
                        Err(_) => {
                            passed += 1;
                        }
                        Ok(_) => {
                            failed += 1;
                            eprintln!(
                                "  FAIL assert_malformed: should have been rejected ({message})"
                            );
                        }
                    },
                    Err(_) => {
                        passed += 1;
                    }
                },

                // assert_unlinkable: component instantiation should fail to link
                wast::WastDirective::AssertUnlinkable {
                    mut module,
                    message,
                    ..
                } => match module.encode() {
                    Ok(binary) => match self.try_instantiate(&binary) {
                        Err(_) => {
                            passed += 1;
                        }
                        Ok(_) => {
                            failed += 1;
                            eprintln!(
                                "  FAIL assert_unlinkable: should have failed to link ({message})"
                            );
                        }
                    },
                    Err(_) => {
                        passed += 1;
                    }
                },

                // assert_exhaustion
                wast::WastDirective::AssertExhaustion { .. } => {
                    failed += 1;
                    eprintln!("  FAIL assert_exhaustion: not implemented");
                }

                // assert_exception
                wast::WastDirective::AssertException { .. } => {
                    failed += 1;
                    eprintln!("  FAIL assert_exception: not implemented");
                }

                // assert_suspension
                wast::WastDirective::AssertSuspension { .. } => {
                    failed += 1;
                    eprintln!("  FAIL assert_suspension: not implemented");
                }

                // bare invoke
                wast::WastDirective::Invoke(invoke) => {
                    let module_name = invoke.module.map(|id| id.name());
                    let has_instance = match module_name {
                        Some(n) => self.named_instances.contains_key(n),
                        None => self.current_instance.is_some(),
                    };
                    if !has_instance {
                        failed += 1;
                        eprintln!("  FAIL invoke {}(): no instance available", invoke.name);
                        continue;
                    }
                    let args = extract_component_args(&invoke);
                    match self.invoke_component(invoke.name, &args, module_name) {
                        Ok(_) => passed += 1,
                        Err(e) => {
                            failed += 1;
                            eprintln!("  FAIL invoke {}(): {e}", invoke.name);
                        }
                    }
                }

                // Unhandled directive type
                _ => {
                    failed += 1;
                    eprintln!("  FAIL: unhandled directive type");
                }
            }
        }

        (passed, failed)
    }
}

/// Convert WastVal arguments to ComponentArg for canonical ABI lowering.
///
/// Scalar types become `ComponentArg::Value(...)`, lists become
/// `ComponentArg::List(...)` recursively.
fn convert_wast_args_to_component(args: &[&WastVal]) -> Vec<ComponentArg> {
    args.iter()
        .filter_map(|arg| convert_single_wast_arg(arg))
        .collect()
}

/// Convert a single WastVal to a ComponentArg.
fn convert_single_wast_arg(arg: &WastVal) -> Option<ComponentArg> {
    match arg {
        WastVal::Bool(v) => Some(ComponentArg::Value(Value::I32(if *v { 1 } else { 0 }))),
        WastVal::S8(v) => Some(ComponentArg::Value(Value::I32(*v as i32))),
        WastVal::U8(v) => Some(ComponentArg::Value(Value::I32(*v as i32))),
        WastVal::S16(v) => Some(ComponentArg::Value(Value::I32(*v as i32))),
        WastVal::U16(v) => Some(ComponentArg::Value(Value::I32(*v as i32))),
        WastVal::S32(v) => Some(ComponentArg::Value(Value::I32(*v))),
        WastVal::U32(v) => Some(ComponentArg::Value(Value::I32(*v as i32))),
        WastVal::S64(v) => Some(ComponentArg::Value(Value::I64(*v))),
        WastVal::U64(v) => Some(ComponentArg::Value(Value::I64(*v as i64))),
        WastVal::F32(v) => Some(ComponentArg::Value(Value::F32(f32::from_bits(v.bits)))),
        WastVal::F64(v) => Some(ComponentArg::Value(Value::F64(f64::from_bits(v.bits)))),
        WastVal::Char(c) => Some(ComponentArg::Value(Value::I32(*c as i32))),
        WastVal::List(items) => {
            let converted: Vec<ComponentArg> = items
                .iter()
                .filter_map(|item| convert_single_wast_arg(item))
                .collect();
            Some(ComponentArg::List(converted))
        }
        _ => None,
    }
}

/// Extract invoke arguments as WastVal references.
fn extract_component_args<'a>(invoke: &'a wast::WastInvoke<'a>) -> Vec<&'a WastVal<'a>> {
    invoke
        .args
        .iter()
        .filter_map(|arg| match arg {
            wast::WastArg::Component(val) => Some(val),
            _ => None,
        })
        .collect()
}

/// Format expected results for error messages.
fn format_expected(expected: &[WastRet]) -> String {
    let parts: Vec<String> = expected
        .iter()
        .map(|e| match e {
            WastRet::Component(val) => format!("{val:?}"),
            WastRet::Core(val) => format!("Core({val:?})"),
            _ => "?".to_string(),
        })
        .collect();
    format!("[{}]", parts.join(", "))
}

/// Check if actual results match expected results.
fn check_results(got: &[ComponentValue], expected: &[WastRet]) -> bool {
    if got.len() != expected.len() {
        return false;
    }
    got.iter().zip(expected).all(|(g, e)| match e {
        WastRet::Component(val) => component_value_matches(g, val),
        WastRet::Core(_) => false,
        _ => false,
    })
}

/// Check if a component value matches an expected WastVal.
fn component_value_matches(got: &ComponentValue, expected: &WastVal) -> bool {
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

fn run_component_test(name: &str, subdir: &str) {
    let path = Path::new("tests/component-model/test")
        .join(subdir)
        .join(format!("{name}.wast"));
    if !path.exists() {
        panic!("component test not found: {}", path.display());
    }

    let mut runner = ComponentTestRunner::new();
    let (passed, failed) = runner.run_wast(&path);

    println!("{name}: {passed} passed, {failed} failed");

    assert_eq!(failed, 0, "{name}: {failed} assertions failed");
}

macro_rules! component_tests {
    ($($name:ident => ($subdir:expr, $file:expr)),* $(,)?) => {
        $(
            #[test]
            fn $name() {
                run_component_test($file, $subdir);
            }
        )*
    };
    (ignored: $($name:ident => ($subdir:expr, $file:expr)),* $(,)?) => {
        $(
            #[test]
            #[ignore]
            fn $name() {
                run_component_test($file, $subdir);
            }
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

    // async (advanced)
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
    // Ignored: wast v245 doesn't support `thread.yield-to` syntax
    // comp_async_trap_if_block_and_sync => ("async", "trap-if-block-and-sync"),
    comp_async_trap_if_done => ("async", "trap-if-done"),
    comp_async_trap_on_reenter => ("async", "trap-on-reenter"),
    comp_async_wait_during_callback => ("async", "wait-during-callback"),
    comp_async_zero_length => ("async", "zero-length"),
}
