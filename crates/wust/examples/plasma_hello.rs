//! Runs JS programs inside Plasma (Boa JS engine compiled to WASM)
//! running inside WUST (our WASM interpreter).
//!
//! Build plasma first:
//!   cargo build -p plasma --target wasm32-unknown-unknown --release
//!
//! Then run:
//!   cargo run -p wust --example plasma_hello --release

use std::sync::{Arc, Mutex};
use wust::runtime::module::ImportKind;
use wust::runtime::{HostFunc, Module, Store, Value};

fn main() {
    let wasm_path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../target/wasm32-unknown-unknown/release/plasma.wasm"
    );
    let wasm_bytes = std::fs::read(wasm_path).expect(
        "failed to read plasma.wasm — did you run: cargo build -p plasma --target wasm32-unknown-unknown --release?"
    );
    let module = Module::from_bytes(&wasm_bytes).expect("failed to parse plasma.wasm");

    run_test(
        &module,
        "hello world",
        r#"console.log("hello world")"#,
        "hello world",
    );

    run_test(
        &module,
        "fibonacci",
        r#"
        function fib(n) {
            if (n <= 1) return n;
            return fib(n - 1) + fib(n - 2);
        }
        console.log(fib(10))
        "#,
        "55",
    );

    println!("\nAll tests passed!");
}

/// Run a JS snippet and assert the captured console.log output matches `expected`.
fn run_test(module: &Module, name: &str, js_source: &str, expected: &str) {
    print!("test {name} ... ");

    let log_output: Arc<Mutex<String>> = Arc::new(Mutex::new(String::new()));
    let host_funcs = build_host_funcs(module, log_output.clone());
    let mut store = Store::new_with_imports(module, host_funcs, vec![])
        .expect("failed to instantiate");

    let ptr = call_alloc(module, &mut store, js_source.len());
    store.memory[ptr..ptr + js_source.len()].copy_from_slice(js_source.as_bytes());

    let result = wust::runtime::exec::invoke(
        module,
        &mut store,
        "eval",
        &[Value::I32(ptr as i32), Value::I32(js_source.len() as i32)],
    )
    .expect("eval trapped");

    let return_code = result[0].unwrap_i32();
    let output = log_output.lock().unwrap();

    assert_eq!(return_code, 0, "{name}: eval returned error");
    assert_eq!(output.as_str(), expected, "{name}: unexpected output");

    println!("ok (output: {output})");
}

/// Build host functions for every function import in the module.
///
/// `host_log` reads a UTF-8 string from WASM memory and appends it
/// to the shared output buffer. All wasm-bindgen stubs are no-ops.
fn build_host_funcs(module: &Module, log_output: Arc<Mutex<String>>) -> Vec<HostFunc> {
    let mut host_funcs: Vec<HostFunc> = Vec::new();

    for import in &module.imports {
        if let ImportKind::Func(type_idx) = &import.kind {
            let func_type = &module.types[*type_idx as usize];
            let has_result = !func_type.results().is_empty();

            if import.name == "host_log" {
                let output = log_output.clone();
                host_funcs.push(Box::new(move |args, memory| {
                    let ptr = args[0].unwrap_i32() as usize;
                    let len = args[1].unwrap_i32() as usize;
                    if let Ok(msg) = std::str::from_utf8(&memory[ptr..ptr + len]) {
                        output.lock().unwrap().push_str(msg);
                    }
                    Ok(vec![])
                }));
            } else if has_result {
                // wasm-bindgen stub that returns a value — return 0.
                host_funcs.push(Box::new(|_args, _memory| Ok(vec![Value::I32(0)])));
            } else {
                // wasm-bindgen stub — no-op.
                host_funcs.push(Box::new(|_args, _memory| Ok(vec![])));
            }
        }
    }

    host_funcs
}

/// Call plasma's `alloc` export to reserve bytes in WASM linear memory.
fn call_alloc(module: &Module, store: &mut Store, size: usize) -> usize {
    let result = wust::runtime::exec::invoke(module, store, "alloc", &[Value::I32(size as i32)])
        .expect("alloc trapped");
    result[0].unwrap_i32() as usize
}
