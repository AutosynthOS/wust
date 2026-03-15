#![cfg(feature = "trace")]

use autosynth_lower::__serde_json as serde_json;

#[test]
fn trace_fib_dump() {
    autosynth_lower::trace::reset();

    let wat = r#"(module
        (func $fib (export "fib") (param $n i32) (result i32)
            (local $a i32)
            (local $b i32)
            (if (i32.le_s (local.get $n) (i32.const 1))
                (then (return (local.get $n)))
            )
            (local.set $a (call $fib (i32.sub (local.get $n) (i32.const 1))))
            (local.set $b (call $fib (i32.sub (local.get $n) (i32.const 2))))
            (i32.add (local.get $a) (local.get $b))
        ))
    "#;
    let wasm = wat::parse_str(wat).expect("parse WAT");
    let module = wust_core::ParsedModule::new(&wasm).expect("parse module");

    use autosynth_backend_aarch64::Aarch64Backend;
    let _jit = wust_codegen::JitModule::<Aarch64Backend>::new(module).expect("compile");

    let events = autosynth_lower::trace::take_trace();

    eprintln!("\n=== TRACE ({} events) ===\n", events.len());
    for (i, e) in events.iter().enumerate() {
        let ty = e.get("type").and_then(|v| v.as_str()).unwrap_or("?");
        match ty {
            "regalloc_state" => {
                // Show first one in full, rest abbreviated
                if i < 140 {
                    eprintln!("[{i:3}] {}", serde_json::to_string_pretty(e).unwrap());
                } else {
                    eprintln!("[{i:3}] regalloc_state (inst: {})",
                        e.get("inst").map(|v| format!("{}", v)).unwrap_or_default());
                }
            }
            _ => {
                eprintln!("[{i:3}] {}", serde_json::to_string(e).unwrap());
            }
        }
    }

    // Basic sanity checks
    assert!(events.len() > 20, "expected many events, got {}", events.len());

    let types: Vec<&str> = events.iter()
        .filter_map(|e| e.get("type").and_then(|v| v.as_str()))
        .collect();

    assert!(types.contains(&"function_start"));
    assert!(types.contains(&"block_start"));
    assert!(types.contains(&"wasm_op"));
    assert!(types.contains(&"ir"));
    assert!(types.contains(&"reg"));
    assert!(types.contains(&"lower_block_start"));
    assert!(types.contains(&"asm"));
    assert!(types.contains(&"regalloc_state"));
    assert!(types.contains(&"function_end"));
}
