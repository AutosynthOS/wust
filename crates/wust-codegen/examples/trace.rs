//! Compile a WAT file and write the trace JSON to viz/static/trace.json.
//!
//! Usage:
//!   cargo run -p wust-codegen --features trace --example trace -- path/to/file.wat
//!
//! If no path is given, compiles the built-in fib function.

#[cfg(not(feature = "trace"))]
fn main() {
    eprintln!("error: must be built with --features trace");
    std::process::exit(1);
}

#[cfg(feature = "trace")]
fn main() {
    use autosynth_backend_aarch64::Aarch64Backend;
    use autosynth_lower::__serde_json as serde_json;

    autosynth_lower::trace::reset();

    let args: Vec<String> = std::env::args().collect();
    let wat_source = if let Some(path) = args.get(1) {
        std::fs::read_to_string(path).unwrap_or_else(|e| {
            eprintln!("error: cannot read {path}: {e}");
            std::process::exit(1);
        })
    } else {
        DEFAULT_FIB.to_string()
    };

    let wasm = wat::parse_str(&wat_source).unwrap_or_else(|e| {
        eprintln!("error: WAT parse failed: {e}");
        std::process::exit(1);
    });

    // Install debugger so dbg_group_idx flows through the backend.
    // The trace reads current_group() for ASM parent attribution.
    let mut dbg = autosynth_codegen::debugger::Debugger::new();
    dbg.add_machine_column("addr", autosynth_codegen::Align::Right);
    dbg.add_machine_column("asm", autosynth_codegen::Align::Left);
    autosynth_codegen::debugger::install(dbg);

    let module = wust_core::ParsedModule::new(&wasm).unwrap_or_else(|e| {
        eprintln!("error: module parse failed: {e}");
        std::process::exit(1);
    });

    let _jit = wust_codegen::JitModule::<Aarch64Backend>::new(module).unwrap_or_else(|e| {
        eprintln!("error: compilation failed: {e}");
        std::process::exit(1);
    });

    let events = autosynth_lower::trace::take_trace();
    let json = serde_json::to_string_pretty(&events).expect("serialize trace");

    // Write to viz/src/lib/trace.json (Vite can import from src/)
    let out_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../viz/src/lib/trace.json");

    std::fs::write(&out_path, &json).unwrap_or_else(|e| {
        eprintln!("error: cannot write {}: {e}", out_path.display());
        std::process::exit(1);
    });

    eprintln!("wrote {} events ({} bytes) to {}", events.len(), json.len(), out_path.display());
}

const DEFAULT_FIB: &str = r#"(module
  (func $fib (export "fib") (param $n i32) (result i32)
    (local $a i32)
    (local $b i32)
    (if (i32.le_s (local.get $n) (i32.const 1))
      (then (return (local.get $n)))
    )
    (local.set $a (call $fib (i32.sub (local.get $n) (i32.const 1))))
    (local.set $b (call $fib (i32.sub (local.get $n) (i32.const 2))))
    (i32.add (local.get $a) (local.get $b))
  )
)"#;
