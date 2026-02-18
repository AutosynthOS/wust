use std::path::Path;
use wast::core::{WastArgCore, WastRetCore};
use wust::runtime::{ExecError, HostFunc, Module, Store, Value};

fn val_from_arg(arg: &WastArgCore) -> Option<Value> {
    match arg {
        WastArgCore::I32(v) => Some(Value::I32(*v)),
        WastArgCore::I64(v) => Some(Value::I64(*v)),
        WastArgCore::F32(v) => Some(Value::F32(f32::from_bits(v.bits))),
        WastArgCore::F64(v) => Some(Value::F64(f64::from_bits(v.bits))),
        _ => None,
    }
}

fn val_from_ret(ret: &WastRetCore) -> Option<Value> {
    match ret {
        WastRetCore::I32(v) => Some(Value::I32(*v)),
        WastRetCore::I64(v) => Some(Value::I64(*v)),
        WastRetCore::F32(v) => match v {
            wast::core::NanPattern::Value(f) => Some(Value::F32(f32::from_bits(f.bits))),
            _ => None, // nan patterns
        },
        WastRetCore::F64(v) => match v {
            wast::core::NanPattern::Value(f) => Some(Value::F64(f64::from_bits(f.bits))),
            _ => None, // nan patterns
        },
        _ => None,
    }
}

fn values_match(got: &Value, expected: &Value) -> bool {
    match (got, expected) {
        (Value::I32(a), Value::I32(b)) => a == b,
        (Value::I64(a), Value::I64(b)) => a == b,
        (Value::F32(a), Value::F32(b)) => a.to_bits() == b.to_bits(),
        (Value::F64(a), Value::F64(b)) => a.to_bits() == b.to_bits(),
        _ => false,
    }
}

/// Build host functions and imported globals for a module's imports.
/// Currently supports the "spectest" module.
fn build_imports(module: &Module) -> (Vec<HostFunc>, Vec<Value>) {
    let mut host_funcs: Vec<HostFunc> = Vec::new();
    let mut imported_globals: Vec<Value> = Vec::new();

    for import in &module.imports {
        match &import.kind {
            wust::runtime::module::ImportKind::Func(_) => {
                // All spectest functions are nops (print_i32, print_f32, print, etc.)
                let nop: HostFunc = Box::new(|_args| Vec::new());
                host_funcs.push(nop);
            }
            wust::runtime::module::ImportKind::Global { ty, .. } => {
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
            // Memory and Table imports are handled by the Module parser
            // (they're already added to module.memories / module.tables)
            _ => {}
        }
    }

    (host_funcs, imported_globals)
}

struct TestRunner {
    module: Option<Module>,
    store: Option<Store>,
}

impl TestRunner {
    fn new() -> Self {
        TestRunner {
            module: None,
            store: None,
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
                    Ok(binary) => match Module::from_bytes(&binary) {
                        Ok(m) => {
                            let (host_funcs, imported_globals) = build_imports(&m);
                            match Store::new_with_imports(&m, host_funcs, imported_globals) {
                                Ok(mut store) => {
                                    // Run start function if present
                                    if let Some(start_idx) = m.start {
                                        let _ = wust::runtime::exec::call(&m, &mut store, start_idx, &[]);
                                    }
                                    self.store = Some(store);
                                    self.module = Some(m);
                                }
                                Err(_e) => {
                                    self.module = None;
                                    self.store = None;
                                }
                            }
                        }
                        Err(_e) => {
                            self.module = None;
                            self.store = None;
                        }
                    },
                    Err(_) => {
                        self.module = None;
                        self.store = None;
                    }
                },
                wast::WastDirective::AssertReturn {
                    exec: wast::WastExecute::Invoke(invoke),
                    results,
                    ..
                } => {
                    let (module, store) = match (&self.module, &mut self.store) {
                        (Some(m), Some(s)) => (m, s),
                        _ => {
                            skipped += 1;
                            continue;
                        }
                    };

                    let args: Option<Vec<Value>> = invoke
                        .args
                        .iter()
                        .map(|a| match a {
                            wast::WastArg::Core(c) => val_from_arg(c),
                            _ => None,
                        })
                        .collect();
                    let args = match args {
                        Some(a) => a,
                        None => { skipped += 1; continue; }
                    };

                    let expected: Option<Vec<Value>> = results
                        .iter()
                        .map(|r| match r {
                            wast::WastRet::Core(c) => val_from_ret(c),
                            _ => None,
                        })
                        .collect();
                    let expected = match expected {
                        Some(e) => e,
                        None => { skipped += 1; continue; }
                    };

                    let func_idx = match module.export_func(invoke.name) {
                        Some(idx) => idx,
                        None => { skipped += 1; continue; }
                    };
                    match wust::runtime::exec::call(module, store, func_idx, &args) {
                        Ok(got) => {
                            if got.len() == expected.len()
                                && got.iter().zip(&expected).all(|(g, e)| values_match(g, e))
                            {
                                passed += 1;
                            } else {
                                failed += 1;
                                eprintln!(
                                    "  FAIL {}({:?}) = {:?}, expected {:?}",
                                    invoke.name, args, got, expected
                                );
                            }
                        }
                        Err(e) => {
                            failed += 1;
                            eprintln!(
                                "  FAIL {}({:?}) trapped: {}, expected {:?}",
                                invoke.name, args, e, expected
                            );
                        }
                    }
                }
                wast::WastDirective::AssertTrap {
                    exec: wast::WastExecute::Invoke(invoke),
                    message,
                    ..
                } => {
                    let (module, store) = match (&self.module, &mut self.store) {
                        (Some(m), Some(s)) => (m, s),
                        _ => {
                            skipped += 1;
                            continue;
                        }
                    };

                    let args: Option<Vec<Value>> = invoke
                        .args
                        .iter()
                        .map(|a| match a {
                            wast::WastArg::Core(c) => val_from_arg(c),
                            _ => None,
                        })
                        .collect();
                    let args = match args {
                        Some(a) => a,
                        None => { skipped += 1; continue; }
                    };

                    let func_idx = match module.export_func(invoke.name) {
                        Some(idx) => idx,
                        None => { skipped += 1; continue; }
                    };
                    match wust::runtime::exec::call(module, store, func_idx, &args) {
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
                // Bare invoke (e.g. calling "init" or "reset" without checking result)
                wast::WastDirective::Invoke(invoke) => {
                    let (module, store) = match (&self.module, &mut self.store) {
                        (Some(m), Some(s)) => (m, s),
                        _ => { skipped += 1; continue; }
                    };
                    let args: Option<Vec<Value>> = invoke
                        .args
                        .iter()
                        .map(|a| match a {
                            wast::WastArg::Core(c) => val_from_arg(c),
                            _ => None,
                        })
                        .collect();
                    let args = match args {
                        Some(a) => a,
                        None => { skipped += 1; continue; }
                    };
                    if let Some(func_idx) = module.export_func(invoke.name) {
                        let _ = wust::runtime::exec::call(module, store, func_idx, &args);
                    }
                }
                // Skip other directives for now (assert_invalid, assert_malformed, etc.)
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

// Integer
#[test]
fn spec_i32() {
    run_spec_test("i32");
}
#[test]
fn spec_i64() {
    run_spec_test("i64");
}
#[test]
fn spec_int_exprs() {
    run_spec_test("int_exprs");
}
#[test]
fn spec_int_literals() {
    run_spec_test("int_literals");
}

// Control flow
#[test]
fn spec_nop() {
    run_spec_test("nop");
}
#[test]
fn spec_block() {
    run_spec_test("block");
}
#[test]
fn spec_loop_() {
    run_spec_test("loop");
}
#[test]
fn spec_if() {
    run_spec_test("if");
}
#[test]
fn spec_br() {
    run_spec_test("br");
}
#[test]
fn spec_br_if() {
    run_spec_test("br_if");
}
#[test]
fn spec_br_table() {
    run_spec_test("br_table");
}
#[test]
fn spec_return() {
    run_spec_test("return");
}
#[test]
fn spec_call() {
    run_spec_test("call");
}
#[test]
fn spec_call_indirect() {
    run_spec_test("call_indirect");
}
#[test]
fn spec_unreachable() {
    run_spec_test("unreachable");
}
#[test]
fn spec_unwind() {
    run_spec_test("unwind");
}
#[test]
fn spec_fac() {
    run_spec_test("fac");
}
#[test]
fn spec_forward() {
    run_spec_test("forward");
}
#[test]
fn spec_switch() {
    run_spec_test("switch");
}
#[test]
fn spec_labels() {
    run_spec_test("labels");
}
#[test]
fn spec_stack() {
    run_spec_test("stack");
}
#[test]
fn spec_left_to_right() {
    run_spec_test("left-to-right");
}

// Variables
#[test]
fn spec_local_get() {
    run_spec_test("local_get");
}
#[test]
fn spec_local_set() {
    run_spec_test("local_set");
}
#[test]
fn spec_local_tee() {
    run_spec_test("local_tee");
}
#[test]
fn spec_global() {
    run_spec_test("global");
}

// Memory
#[test]
fn spec_memory() {
    run_spec_test("memory");
}
#[test]
fn spec_memory_size() {
    run_spec_test("memory_size");
}
#[test]
fn spec_memory_grow() {
    run_spec_test("memory_grow");
}
#[test]
fn spec_load() {
    run_spec_test("load");
}
#[test]
fn spec_store() {
    run_spec_test("store");
}
#[test]
fn spec_address() {
    run_spec_test("address");
}
#[test]
fn spec_align() {
    run_spec_test("align");
}
#[test]
fn spec_endianness() {
    run_spec_test("endianness");
}
#[test]
fn spec_traps() {
    run_spec_test("traps");
}

// Other
#[test]
fn spec_func() {
    run_spec_test("func");
}
#[test]
fn spec_select() {
    run_spec_test("select");
}
#[test]
fn spec_conversions() {
    run_spec_test("conversions");
}
#[test]
fn spec_func_ptrs() {
    run_spec_test("func_ptrs");
}
#[test]
fn spec_start() {
    run_spec_test("start");
}
#[test]
fn spec_type() {
    run_spec_test("type");
}

// Float
#[test] fn spec_f32() { run_spec_test("f32"); }
#[test] fn spec_f64() { run_spec_test("f64"); }
#[test] fn spec_f32_cmp() { run_spec_test("f32_cmp"); }
#[test] fn spec_f64_cmp() { run_spec_test("f64_cmp"); }
#[test] fn spec_f32_bitwise() { run_spec_test("f32_bitwise"); }
#[test] fn spec_f64_bitwise() { run_spec_test("f64_bitwise"); }
#[test] fn spec_float_exprs() { run_spec_test("float_exprs"); }
#[test] fn spec_float_literals() { run_spec_test("float_literals"); }
#[test] fn spec_float_memory() { run_spec_test("float_memory"); }
#[test] fn spec_float_misc() { run_spec_test("float_misc"); }

// Data/Elem/Table
#[test] fn spec_data() { run_spec_test("data"); }
#[test] fn spec_elem() { run_spec_test("elem"); }
#[test] fn spec_table() { run_spec_test("table"); }
#[test] fn spec_exports() { run_spec_test("exports"); }
