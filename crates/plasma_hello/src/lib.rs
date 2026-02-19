pub mod polyfills;

use std::sync::{Arc, Mutex};
use wust::runtime::module::ImportKind;
use wust::runtime::{HostFunc, Module, Store, Value};

/// Load and parse the plasma WASM module from the build output directory.
///
/// Panics if the file does not exist. Callers should build plasma first:
///   cargo build -p plasma --target wasm32-unknown-unknown --release
pub fn load_plasma_module() -> Module {
    let wasm_path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../target/wasm32-unknown-unknown/release/plasma.wasm"
    );
    let wasm_bytes = std::fs::read(wasm_path).expect(
        "failed to read plasma.wasm — did you run: \
         cargo build -p plasma --target wasm32-unknown-unknown --release?",
    );
    Module::from_bytes(&wasm_bytes).expect("failed to parse plasma.wasm")
}

/// Collected output from console.log calls during JS evaluation.
pub struct EvalResult {
    /// The return code from plasma's eval function (0 = success, 1 = error).
    pub return_code: i32,
    /// All console.log output concatenated together.
    pub log_output: String,
}

/// Evaluate a JS source string inside the plasma runtime.
///
/// Instantiates a fresh plasma WASM module, copies the JS source into
/// linear memory, and calls `eval`. Console.log output is captured and
/// returned along with the return code.
///
/// # Arguments
/// * `module` - a pre-parsed plasma WASM module
/// * `js_source` - the JavaScript source code to evaluate
pub fn eval_js(module: &Module, js_source: &str) -> EvalResult {
    let log_output: Arc<Mutex<String>> = Arc::new(Mutex::new(String::new()));
    let host_funcs = build_host_funcs(module, log_output.clone());
    let mut store =
        Store::new_with_imports(module, host_funcs, vec![], vec![]).expect("failed to instantiate plasma");

    let ptr = call_alloc(module, &mut store, js_source.len());
    store.memory[ptr..ptr + js_source.len()].copy_from_slice(js_source.as_bytes());

    let result = wust::runtime::exec::invoke(
        module,
        &mut store,
        "eval",
        &[Value::I32(ptr as i32), Value::I32(js_source.len() as i32)],
    );

    let return_code = match result {
        Ok(values) => values[0].unwrap_i32(),
        Err(e) => {
            let mut output = log_output.lock().unwrap();
            output.push_str(&format!("[TRAP: {e}]"));
            -1
        }
    };

    let output = log_output.lock().unwrap().clone();
    EvalResult {
        return_code,
        log_output: output,
    }
}

/// Evaluate JS with Node.js polyfills prepended.
///
/// This is identical to [`eval_js`] but first injects polyfills for
/// `process`, `EventEmitter`, timers, `TextEncoder`/`TextDecoder`,
/// `Buffer`, and `URL`/`URLSearchParams` before the user's source code.
///
/// # Arguments
/// * `module` - a pre-parsed plasma WASM module
/// * `js_source` - the JavaScript source code to evaluate
pub fn eval_js_with_polyfills(module: &Module, js_source: &str) -> EvalResult {
    let preamble = polyfills::all_polyfills();
    let full_source = format!("{preamble}\n{js_source}");
    eval_js(module, &full_source)
}

/// Build host functions for every function import in the module.
///
/// `host_log` reads a UTF-8 string from WASM memory and appends it
/// to the shared output buffer. All other imports get no-op stubs.
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
                    Ok(Vec::new())
                }));
            } else if has_result {
                host_funcs.push(Box::new(|_args, _memory| Ok(vec![Value::I32(0)])));
            } else {
                host_funcs.push(Box::new(|_args, _memory| Ok(Vec::new())));
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
