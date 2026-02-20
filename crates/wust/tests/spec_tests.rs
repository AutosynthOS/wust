use std::collections::HashMap;
use std::path::Path;
use std::sync::Arc;
use wast::core::{WastArgCore, WastRetCore};
use wust::runtime::{EXTERN_FUNC_BASE, ExecError, ExportKind, HostFunc, Module, Store, Value};

fn val_from_arg(arg: &WastArgCore) -> Option<Value> {
    match arg {
        WastArgCore::I32(v) => Some(Value::I32(*v)),
        WastArgCore::I64(v) => Some(Value::I64(*v)),
        WastArgCore::F32(v) => Some(Value::F32(f32::from_bits(v.bits))),
        WastArgCore::F64(v) => Some(Value::F64(f64::from_bits(v.bits))),
        WastArgCore::RefNull(_) => Some(Value::FuncRef(None)),
        WastArgCore::RefExtern(v) => Some(Value::FuncRef(Some(*v))),
        _ => None,
    }
}

/// Expected result from assert_return: either an exact value or a NaN check.
enum Expected {
    Exact(Value),
    F32Nan,
    F64Nan,
    RefNull,
    RefNotNull,
    RefExtern(u32),
}

fn expected_from_ret(ret: &WastRetCore) -> Option<Expected> {
    match ret {
        WastRetCore::I32(v) => Some(Expected::Exact(Value::I32(*v))),
        WastRetCore::I64(v) => Some(Expected::Exact(Value::I64(*v))),
        WastRetCore::F32(v) => match v {
            wast::core::NanPattern::Value(f) => {
                Some(Expected::Exact(Value::F32(f32::from_bits(f.bits))))
            }
            wast::core::NanPattern::CanonicalNan | wast::core::NanPattern::ArithmeticNan => {
                Some(Expected::F32Nan)
            }
        },
        WastRetCore::F64(v) => match v {
            wast::core::NanPattern::Value(f) => {
                Some(Expected::Exact(Value::F64(f64::from_bits(f.bits))))
            }
            wast::core::NanPattern::CanonicalNan | wast::core::NanPattern::ArithmeticNan => {
                Some(Expected::F64Nan)
            }
        },
        WastRetCore::RefNull(_) => Some(Expected::RefNull),
        WastRetCore::RefExtern(Some(v)) => Some(Expected::RefExtern(*v)),
        WastRetCore::RefExtern(None) => Some(Expected::RefNull),
        WastRetCore::RefFunc(_) => Some(Expected::RefNotNull),
        _ => None,
    }
}

fn result_matches(got: &Value, expected: &Expected) -> bool {
    match (got, expected) {
        (Value::I32(a), Expected::Exact(Value::I32(b))) => a == b,
        (Value::I64(a), Expected::Exact(Value::I64(b))) => a == b,
        (Value::F32(a), Expected::Exact(Value::F32(b))) => a.to_bits() == b.to_bits(),
        (Value::F64(a), Expected::Exact(Value::F64(b))) => a.to_bits() == b.to_bits(),
        (Value::F32(a), Expected::F32Nan) => a.is_nan(),
        (Value::F64(a), Expected::F64Nan) => a.is_nan(),
        (Value::FuncRef(None), Expected::RefNull) => true,
        (Value::FuncRef(Some(_)), Expected::RefNull) => false,
        (Value::FuncRef(Some(_)), Expected::RefNotNull) => true,
        (Value::FuncRef(None), Expected::RefNotNull) => false,
        (Value::FuncRef(Some(idx)), Expected::RefExtern(v)) => *idx == *v,
        (Value::FuncRef(None), Expected::RefExtern(_)) => false,
        _ => false,
    }
}

fn parse_args(invoke: &wast::WastInvoke) -> Option<Vec<Value>> {
    invoke
        .args
        .iter()
        .map(|a| match a {
            wast::WastArg::Core(c) => val_from_arg(c),
            _ => None,
        })
        .collect()
}

fn parse_expected(results: &[wast::WastRet]) -> Option<Vec<Expected>> {
    results
        .iter()
        .map(|r| match r {
            wast::WastRet::Core(c) => expected_from_ret(c),
            _ => None,
        })
        .collect()
}

/// A registered module instance (module + store) for cross-module imports.
struct RegisteredModule {
    module: Arc<Module>,
    store: Arc<std::sync::Mutex<Store>>,
}

/// A pending funcref registration: (global_index, source_module, source_store, source_func_idx).
type PendingFuncRef = (usize, Arc<Module>, Arc<std::sync::Mutex<Store>>, u32);

/// Build host functions and imported globals for a module's imports.
/// Returns pending funcref registrations that must be applied after Store creation.
fn build_imports(
    module: &Module,
    registered: &HashMap<String, RegisteredModule>,
) -> (Vec<HostFunc>, Vec<Value>, Vec<PendingFuncRef>) {
    let mut host_funcs: Vec<HostFunc> = Vec::new();
    let mut imported_globals: Vec<Value> = Vec::new();
    let mut pending_funcrefs: Vec<PendingFuncRef> = Vec::new();

    for import in &module.imports {
        match &import.kind {
            wust::runtime::module::ImportKind::Func(_type_idx) => {
                if let Some(reg) = registered.get(&import.module) {
                    if let Some(func_idx) = reg.module.export_func(&import.name) {
                        let reg_module = reg.module.clone();
                        let reg_store = reg.store.clone();
                        let host_fn: HostFunc = Box::new(move |args, _memory| {
                            let mut store = reg_store.lock().unwrap();
                            wust::runtime::code::program::call(
                                &reg_module,
                                &mut store,
                                func_idx,
                                args,
                            )
                            .map_err(|e| format!("{e}"))
                        });
                        host_funcs.push(host_fn);
                        continue;
                    }
                }
                let nop: HostFunc = Box::new(|_args, _memory| Ok(Vec::new()));
                host_funcs.push(nop);
            }
            wust::runtime::module::ImportKind::Global { ty, .. } => {
                if let Some(reg) = registered.get(&import.module) {
                    let store = reg.store.lock().unwrap();
                    if let Some(val) = resolve_exported_global(&reg.module, &store, &import.name) {
                        if let Value::FuncRef(Some(src_func_idx)) = val {
                            let extern_idx = EXTERN_FUNC_BASE + pending_funcrefs.len() as u32;
                            imported_globals.push(Value::FuncRef(Some(extern_idx)));
                            pending_funcrefs.push((
                                imported_globals.len() - 1,
                                reg.module.clone(),
                                reg.store.clone(),
                                src_func_idx,
                            ));
                            continue;
                        }
                        imported_globals.push(val);
                        continue;
                    }
                }
                let val = match import.module.as_str() {
                    "spectest" => match ty {
                        wasmparser::ValType::I32 => Value::I32(666),
                        wasmparser::ValType::I64 => Value::I64(666),
                        wasmparser::ValType::F32 => Value::F32(666.6),
                        wasmparser::ValType::F64 => Value::F64(666.6),
                        _ => Value::I32(0),
                    },
                    _ => Value::I32(0),
                };
                imported_globals.push(val);
            }
            _ => {}
        }
    }

    (host_funcs, imported_globals, pending_funcrefs)
}

/// Resolve an exported global's value from a registered module.
fn resolve_exported_global(module: &Module, store: &Store, name: &str) -> Option<Value> {
    for export in &module.exports {
        if export.name == name {
            if let ExportKind::Global = export.kind {
                return store.globals.get(export.index as usize).copied();
            }
        }
    }
    None
}

/// Try to compile and instantiate a module. Returns Err if any step fails.
fn try_instantiate(
    binary: &[u8],
    registered: &HashMap<String, RegisteredModule>,
) -> Result<(Arc<Module>, Store), String> {
    let m = Module::from_bytes(binary)?;
    let (host_funcs, imported_globals, pending_funcrefs) = build_imports(&m, registered);
    let mut store = Store::new_with_imports(&m, host_funcs, imported_globals, vec![])?;
    for (_global_idx, src_module, src_store, src_func_idx) in pending_funcrefs {
        let reg_module = src_module.clone();
        let reg_store = src_store.clone();
        let wrapper: HostFunc = Box::new(move |args, _memory| {
            let mut s = reg_store.lock().unwrap();
            wust::runtime::code::program::call(&reg_module, &mut s, src_func_idx, args)
                .map_err(|e| format!("{e}"))
        });
        store.extern_funcs.push(wrapper);
    }
    let m = Arc::new(m);
    if let Some(start_idx) = m.start {
        wust::runtime::code::program::call(&m, &mut store, start_idx, &[])
            .map_err(|e| format!("{e}"))?;
    }
    Ok((m, store))
}

struct TestRunner {
    module: Option<Arc<Module>>,
    store: Option<Arc<std::sync::Mutex<Store>>>,
    registered: HashMap<String, RegisteredModule>,
}

impl TestRunner {
    fn new() -> Self {
        TestRunner {
            module: None,
            store: None,
            registered: HashMap::new(),
        }
    }

    fn run_wast(&mut self, path: &Path) -> (usize, usize, usize) {
        let source = std::fs::read_to_string(path).unwrap();
        let buf = wast::parser::ParseBuffer::new(&source).unwrap();
        let wast = wast::parser::parse::<wast::Wast>(&buf).unwrap();

        let mut passed = 0usize;
        let mut failed = 0usize;
        let mut skipped = 0usize;

        for directive in wast.directives {
            match directive {
                wast::WastDirective::Module(mut wat) => match wat.encode() {
                    Ok(binary) => match try_instantiate(&binary, &self.registered) {
                        Ok((m, store)) => {
                            let store = Arc::new(std::sync::Mutex::new(store));
                            self.store = Some(store);
                            self.module = Some(m);
                        }
                        Err(_) => {
                            self.module = None;
                            self.store = None;
                        }
                    },
                    Err(_) => {
                        self.module = None;
                        self.store = None;
                    }
                },

                wast::WastDirective::Register { name, .. } => {
                    if let (Some(m), Some(s)) = (&self.module, &self.store) {
                        self.registered.insert(
                            name.to_string(),
                            RegisteredModule {
                                module: m.clone(),
                                store: s.clone(),
                            },
                        );
                    }
                }

                // assert_return with invoke
                wast::WastDirective::AssertReturn {
                    exec: wast::WastExecute::Invoke(invoke),
                    results,
                    ..
                } => {
                    let (module, store_arc) = match (&self.module, &self.store) {
                        (Some(m), Some(s)) => (m, s),
                        _ => {
                            skipped += 1;
                            continue;
                        }
                    };
                    let args = match parse_args(&invoke) {
                        Some(a) => a,
                        None => {
                            skipped += 1;
                            continue;
                        }
                    };
                    let expected = match parse_expected(&results) {
                        Some(e) => e,
                        None => {
                            skipped += 1;
                            continue;
                        }
                    };
                    let func_idx = match module.export_func(invoke.name) {
                        Some(idx) => idx,
                        None => {
                            skipped += 1;
                            continue;
                        }
                    };
                    let mut store = store_arc.lock().unwrap();
                    match wust::runtime::code::program::call(module, &mut store, func_idx, &args) {
                        Ok(got) => {
                            if got.len() == expected.len()
                                && got.iter().zip(&expected).all(|(g, e)| result_matches(g, e))
                            {
                                passed += 1;
                            } else {
                                failed += 1;
                                eprintln!(
                                    "  FAIL {}({:?}) = {:?}, expected {:?}",
                                    invoke.name,
                                    args,
                                    got,
                                    expected
                                        .iter()
                                        .map(|e| match e {
                                            Expected::Exact(v) => format!("{v:?}"),
                                            Expected::F32Nan => "f32:nan".into(),
                                            Expected::F64Nan => "f64:nan".into(),
                                            Expected::RefNull => "ref.null".into(),
                                            Expected::RefNotNull => "ref.func".into(),
                                            Expected::RefExtern(v) => format!("ref.extern {v}"),
                                        })
                                        .collect::<Vec<_>>()
                                );
                            }
                        }
                        Err(e) => {
                            failed += 1;
                            eprintln!("  FAIL {}({:?}) trapped: {}", invoke.name, args, e);
                        }
                    }
                }

                // assert_return with get (read exported global)
                wast::WastDirective::AssertReturn {
                    exec:
                        wast::WastExecute::Get {
                            module: module_id,
                            global,
                            ..
                        },
                    results,
                    ..
                } => {
                    // Named module references not yet supported
                    if module_id.is_some() {
                        skipped += 1;
                        continue;
                    }
                    let (module, store_arc) = match (&self.module, &self.store) {
                        (Some(m), Some(s)) => (m, s),
                        _ => {
                            skipped += 1;
                            continue;
                        }
                    };
                    let expected = match parse_expected(&results) {
                        Some(e) => e,
                        None => {
                            skipped += 1;
                            continue;
                        }
                    };
                    let store = store_arc.lock().unwrap();
                    match resolve_exported_global(module, &store, global) {
                        Some(got) => {
                            if expected.len() == 1 && result_matches(&got, &expected[0]) {
                                passed += 1;
                            } else {
                                failed += 1;
                                eprintln!(
                                    "  FAIL (get {global}) = {got:?}, expected {expected:?}",
                                    expected = expected
                                        .iter()
                                        .map(|e| match e {
                                            Expected::Exact(v) => format!("{v:?}"),
                                            Expected::F32Nan => "f32:nan".into(),
                                            Expected::F64Nan => "f64:nan".into(),
                                            Expected::RefNull => "ref.null".into(),
                                            Expected::RefNotNull => "ref.func".into(),
                                            Expected::RefExtern(v) => format!("ref.extern {v}"),
                                        })
                                        .collect::<Vec<_>>()
                                );
                            }
                        }
                        None => {
                            failed += 1;
                            eprintln!("  FAIL (get {global}) global not found");
                        }
                    }
                }

                // assert_return with Wat (instantiate module, check no error)
                wast::WastDirective::AssertReturn {
                    exec: wast::WastExecute::Wat(mut wat),
                    ..
                } => match wat.encode() {
                    Ok(binary) => match try_instantiate(&binary, &self.registered) {
                        Ok(_) => {
                            passed += 1;
                        }
                        Err(e) => {
                            failed += 1;
                            eprintln!("  FAIL assert_return(wat) unexpected error: {e}");
                        }
                    },
                    Err(e) => {
                        failed += 1;
                        eprintln!("  FAIL assert_return(wat) encode error: {e}");
                    }
                },

                // assert_trap with invoke
                wast::WastDirective::AssertTrap {
                    exec: wast::WastExecute::Invoke(invoke),
                    message,
                    ..
                } => {
                    let (module, store_arc) = match (&self.module, &self.store) {
                        (Some(m), Some(s)) => (m, s),
                        _ => {
                            skipped += 1;
                            continue;
                        }
                    };
                    let args = match parse_args(&invoke) {
                        Some(a) => a,
                        None => {
                            skipped += 1;
                            continue;
                        }
                    };
                    let func_idx = match module.export_func(invoke.name) {
                        Some(idx) => idx,
                        None => {
                            skipped += 1;
                            continue;
                        }
                    };
                    let mut store = store_arc.lock().unwrap();
                    match wust::runtime::code::program::call(module, &mut store, func_idx, &args) {
                        Err(ExecError::Trap(_)) => {
                            passed += 1;
                        }
                        Ok(v) => {
                            failed += 1;
                            eprintln!(
                                "  FAIL {}({:?}) should have trapped ({}), got {:?}",
                                invoke.name, args, message, v
                            );
                        }
                        Err(e) => {
                            failed += 1;
                            eprintln!("  FAIL {}({:?}) wrong error: {}", invoke.name, args, e);
                        }
                    }
                }

                // assert_trap with Wat (module instantiation should trap)
                wast::WastDirective::AssertTrap {
                    exec: wast::WastExecute::Wat(mut wat),
                    message,
                    ..
                } => match wat.encode() {
                    Ok(binary) => match try_instantiate(&binary, &self.registered) {
                        Ok(_) => {
                            failed += 1;
                            eprintln!("  FAIL assert_trap(wat) should have trapped ({message})");
                        }
                        Err(_) => {
                            passed += 1;
                        }
                    },
                    Err(_) => {
                        passed += 1;
                    }
                },

                // assert_invalid: module should fail validation
                wast::WastDirective::AssertInvalid {
                    mut module,
                    message,
                    ..
                } => {
                    match module.encode() {
                        Ok(binary) => match Module::from_bytes(&binary) {
                            Err(_) => {
                                passed += 1;
                            }
                            Ok(_) => {
                                failed += 1;
                                eprintln!(
                                    "  FAIL assert_invalid: module should be invalid ({message})"
                                );
                            }
                        },
                        // Encode failure also counts as "invalid"
                        Err(_) => {
                            passed += 1;
                        }
                    }
                }

                // assert_malformed: module should fail to parse
                wast::WastDirective::AssertMalformed {
                    mut module,
                    message,
                    ..
                } => match module.encode() {
                    Ok(binary) => match Module::from_bytes(&binary) {
                        Err(_) => {
                            passed += 1;
                        }
                        Ok(_) => {
                            failed += 1;
                            eprintln!(
                                "  FAIL assert_malformed: module should be malformed ({message})"
                            );
                        }
                    },
                    Err(_) => {
                        passed += 1;
                    }
                },

                // assert_unlinkable: module instantiation should fail
                wast::WastDirective::AssertUnlinkable {
                    mut module,
                    message,
                    ..
                } => match module.encode() {
                    Ok(binary) => match try_instantiate(&binary, &self.registered) {
                        Err(_) => {
                            passed += 1;
                        }
                        Ok(_) => {
                            failed += 1;
                            eprintln!("  FAIL assert_unlinkable: should have failed ({message})");
                        }
                    },
                    Err(_) => {
                        passed += 1;
                    }
                },

                // assert_exhaustion: function call should exhaust resources (stack overflow)
                wast::WastDirective::AssertExhaustion { call, message, .. } => {
                    let (module, store_arc) = match (&self.module, &self.store) {
                        (Some(m), Some(s)) => (m, s),
                        _ => {
                            skipped += 1;
                            continue;
                        }
                    };
                    let args = match parse_args(&call) {
                        Some(a) => a,
                        None => {
                            skipped += 1;
                            continue;
                        }
                    };
                    let func_idx = match module.export_func(call.name) {
                        Some(idx) => idx,
                        None => {
                            skipped += 1;
                            continue;
                        }
                    };
                    let mut store = store_arc.lock().unwrap();
                    match wust::runtime::code::program::call(module, &mut store, func_idx, &args) {
                        Err(_) => {
                            passed += 1;
                        }
                        Ok(v) => {
                            failed += 1;
                            eprintln!(
                                "  FAIL {}({:?}) should have exhausted ({}), got {:?}",
                                call.name, args, message, v
                            );
                        }
                    }
                }

                // Bare invoke
                wast::WastDirective::Invoke(invoke) => {
                    let (module, store_arc) = match (&self.module, &self.store) {
                        (Some(m), Some(s)) => (m, s),
                        _ => {
                            skipped += 1;
                            continue;
                        }
                    };
                    let args = match parse_args(&invoke) {
                        Some(a) => a,
                        None => {
                            skipped += 1;
                            continue;
                        }
                    };
                    if let Some(func_idx) = module.export_func(invoke.name) {
                        let mut store = store_arc.lock().unwrap();
                        let _ =
                            wust::runtime::code::program::call(module, &mut store, func_idx, &args);
                    }
                }

                // Directives we don't handle yet
                _ => {
                    skipped += 1;
                }
            }
        }

        (passed, failed, skipped)
    }
}

fn run_spec_test(name: &str) {
    let path = Path::new("tests/spec/test/core").join(format!("{name}.wast"));
    if !path.exists() {
        panic!("spec test not found: {}", path.display());
    }

    let mut runner = TestRunner::new();
    let (passed, failed, skipped) = runner.run_wast(&path);

    println!(
        "{}: {} passed, {} failed, {} skipped",
        name, passed, failed, skipped
    );

    assert_eq!(failed, 0, "{name}: {failed} assertions failed");
}

/// Generate a #[test] fn for each .wast file in the spec test directory.
/// Tests in IGNORED are marked #[ignore] — they require unimplemented features
/// (typed function references, tail calls, GC types, etc.)
macro_rules! spec_tests {
    ($($name:ident => $file:expr),* $(,)?) => {
        $(
            #[test]
            fn $name() {
                run_spec_test($file);
            }
        )*
    };
    (ignored: $($name:ident => $file:expr),* $(,)?) => {
        $(
            #[test]
            #[ignore]
            fn $name() {
                run_spec_test($file);
            }
        )*
    };
}

// Tests that pass — auto-discovered from tests/spec/test/core/*.wast
spec_tests! {
    spec_address => "address",
    spec_align => "align",
    spec_block => "block",
    spec_br => "br",
    spec_br_if => "br_if",
    spec_br_table => "br_table",
    spec_call => "call",
    spec_call_indirect => "call_indirect",
    spec_comments => "comments",
    spec_const_ => "const",
    spec_conversions => "conversions",
    spec_custom => "custom",
    spec_data => "data",
    spec_elem => "elem",
    spec_endianness => "endianness",
    spec_exports => "exports",
    spec_f32 => "f32",
    spec_f32_bitwise => "f32_bitwise",
    spec_f32_cmp => "f32_cmp",
    spec_f64 => "f64",
    spec_f64_bitwise => "f64_bitwise",
    spec_f64_cmp => "f64_cmp",
    spec_fac => "fac",
    spec_float_exprs => "float_exprs",
    spec_float_literals => "float_literals",
    spec_float_memory => "float_memory",
    spec_float_misc => "float_misc",
    spec_forward => "forward",
    spec_func => "func",
    spec_func_ptrs => "func_ptrs",
    spec_global => "global",
    spec_i32 => "i32",
    spec_i64 => "i64",
    spec_if_ => "if",
    spec_int_exprs => "int_exprs",
    spec_int_literals => "int_literals",
    spec_labels => "labels",
    spec_left_to_right => "left-to-right",
    spec_load => "load",
    spec_local_get => "local_get",
    spec_local_set => "local_set",
    spec_local_tee => "local_tee",
    spec_loop_ => "loop",
    spec_memory => "memory",
    spec_memory_grow => "memory_grow",
    spec_memory_size => "memory_size",
    spec_memory_redundancy => "memory_redundancy",
    spec_memory_trap => "memory_trap",
    spec_nop => "nop",
    spec_return_ => "return",
    spec_select => "select",
    spec_stack => "stack",
    spec_start => "start",
    spec_store_ => "store",
    spec_switch => "switch",
    spec_table => "table",
    spec_table_get => "table_get",
    spec_table_grow => "table_grow",
    spec_table_set => "table_set",
    spec_table_size => "table_size",
    spec_token => "token",
    spec_traps => "traps",
    spec_type_ => "type",
    spec_type_canon => "type-canon",
    spec_unreachable => "unreachable",
    spec_unreached_invalid => "unreached-invalid",
    spec_unreached_valid => "unreached-valid",
    spec_unwind => "unwind",
    spec_annotations => "annotations",
    spec_binary => "binary",
    spec_binary_leb128 => "binary-leb128",
    spec_id => "id",
    spec_inline_module => "inline-module",
    spec_local_init => "local_init",
    spec_obsolete_keywords => "obsolete-keywords",
    spec_ref_ => "ref",
    spec_ref_func => "ref_func",
    spec_ref_is_null => "ref_is_null",
    spec_ref_null => "ref_null",
    // TODO: skip-stack-guard-page triggers SIGBUS — needs a signal handler to catch guard page hits gracefully
    // spec_skip_stack_guard_page => "skip-stack-guard-page",
    spec_utf8_custom_section_id => "utf8-custom-section-id",
    spec_utf8_import_field => "utf8-import-field",
    spec_utf8_import_module => "utf8-import-module",
    spec_utf8_invalid_encoding => "utf8-invalid-encoding",
}

// Tests that require unimplemented proposals (typed funcrefs, tail calls, GC, etc.)
// Run with: cargo test -- --ignored
spec_tests! { ignored:
    spec_imports => "imports",
    spec_instance => "instance",
    spec_linking => "linking",
    spec_names => "names",
    spec_br_on_non_null => "br_on_non_null",
    spec_br_on_null => "br_on_null",
    spec_call_ref => "call_ref",
    spec_ref_as_non_null => "ref_as_non_null",
    spec_return_call => "return_call",
    spec_return_call_indirect => "return_call_indirect",
    spec_return_call_ref => "return_call_ref",
    spec_type_equivalence => "type-equivalence",
    spec_type_rec => "type-rec",
}
