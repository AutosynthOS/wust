pub mod polyfills;

use wust::runtime::exec;
use wust::runtime::{HostFunc, Module, Store, Value};

/// Load and parse the plasma core module from the build output directory.
///
/// Uses `plasma.wasm` (core module), not the componentized version,
/// so that host functions get direct memory access.
///
/// Panics if the file does not exist. Build with:
///   make -C <repo_root> plasma
fn load_plasma_module() -> Module {
    let wasm_path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../target/wasm32-unknown-unknown/release/plasma.wasm"
    );
    let wasm_bytes =
        std::fs::read(wasm_path).expect("failed to read plasma.wasm — run: make plasma");
    Module::from_bytes(&wasm_bytes).unwrap()
}

/// Create a host function for `host-log` that reads UTF-8 from memory.
///
/// When plasma calls `host_log(ptr, len)`, this reads `len` bytes
/// starting at `ptr` from the module's linear memory and prints them
/// to stderr.
fn make_host_log() -> HostFunc {
    Box::new(|args: &[Value], memory: &mut [u8]| {
        let ptr = match args.first() {
            Some(Value::I32(v)) => *v as u32 as usize,
            other => return Err(format!("host-log: expected i32 ptr, got {other:?}")),
        };
        let len = match args.get(1) {
            Some(Value::I32(v)) => *v as u32 as usize,
            other => return Err(format!("host-log: expected i32 len, got {other:?}")),
        };
        let end = ptr.checked_add(len).ok_or("host-log: ptr+len overflow")?;
        if end > memory.len() {
            return Err(format!(
                "host-log: out of bounds: ptr={ptr} len={len} memory={}",
                memory.len()
            ));
        }
        let bytes = &memory[ptr..end];
        match std::str::from_utf8(bytes) {
            Ok(s) => eprintln!("[plasma] {s}"),
            Err(_) => eprintln!("[plasma] <invalid utf-8: {} bytes>", len),
        }
        Ok(vec![])
    })
}

/// Evaluate a JavaScript source string inside the plasma runtime.
///
/// Prepends all polyfills, then feeds the combined source into the
/// plasma module's `eval` export. Returns `0` on success, `1` on
/// JS error.
///
/// # Examples
/// ```no_run
/// let result = plasma_hello::eval_js("1 + 1");
/// assert_eq!(result, 0);
/// ```
pub fn eval_js(js: &str) -> i32 {
    // Polyfills are loaded inside plasma via modules::register_modules(),
    // so we no longer prepend them here.
    let full_source = js;

    let module = load_plasma_module();
    let host_funcs = vec![make_host_log()];
    let mut store = Store::new_with_imports(&module, host_funcs, vec![], vec![])
        .expect("failed to create store");

    // Call alloc to reserve space for the JS source
    let source_bytes = full_source.as_bytes();
    let len = source_bytes.len();
    let alloc_idx = module
        .export_func("alloc")
        .expect("plasma module missing 'alloc' export");
    let alloc_result = exec::call(&module, &mut store, alloc_idx, &[Value::I32(len as i32)])
        .expect("alloc call failed");
    let ptr = match alloc_result.first() {
        Some(Value::I32(v)) => *v,
        other => panic!("alloc returned unexpected: {other:?}"),
    };

    // Write JS source bytes into linear memory
    store.memory[ptr as usize..ptr as usize + len].copy_from_slice(source_bytes);

    // Call eval
    let eval_idx = module
        .export_func("eval")
        .expect("plasma module missing 'eval' export");
    let eval_result = exec::call(
        &module,
        &mut store,
        eval_idx,
        &[Value::I32(ptr), Value::I32(len as i32)],
    )
    .expect("eval call failed");
    match eval_result.first() {
        Some(Value::I32(v)) => *v,
        other => panic!("eval returned unexpected: {other:?}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_eval_simple() {
        let result = eval_js("1 + 1");
        assert_eq!(result, 0);
    }

    #[test]
    fn test_eval_console_log() {
        let result = eval_js("console.log('hello from plasma')");
        assert_eq!(result, 0);
    }

    #[test]
    fn test_eval_error() {
        let result = eval_js("throw new Error('test error')");
        assert_eq!(result, 1);
    }

    #[test]
    fn bench_loop_wust() {
        let js = r#"
let sum = 0;
for (let i = 0; i < 1000; i++) {
    sum += i * i;
}
console.log('sum=' + sum);
"#;
        let start = std::time::Instant::now();
        let result = eval_js(js);
        let elapsed = start.elapsed();
        eprintln!("wust: result={result}, elapsed={elapsed:?}");
        assert_eq!(result, 0);
    }

    #[test]
    #[ignore] // hits execution step limit — boa-in-wasm is too slow for 1.5MB bundle
    fn test_eval_discord_bundle() {
        let bundle = include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/discord-bot/bundle.js"
        ));
        let result = eval_js(bundle);
        eprintln!("discord bundle eval result: {result}");
    }

    #[test]
    fn test_eval_medium_module() {
        // Generate ~1000 lines of valid ESM to test parse scaling
        let mut js = String::new();
        for i in 0..1000 {
            js.push_str(&format!("var x{i} = {i};\n"));
        }
        js.push_str("console.log('parsed 1000 vars');\n");
        let result = eval_js(&js);
        assert_eq!(result, 0);
    }
}
