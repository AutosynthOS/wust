use std::time::Instant;
use wust::{Engine, JitCompiler, JitModule, Linker, Module, Store, Val};

const ACK_WAT: &str = r#"
(module
  (func $ack (export "ack") (param $m i32) (param $n i32) (result i32)
    (if (result i32) (i32.eqz (local.get $m))
      (then
        (i32.add (local.get $n) (i32.const 1))
      )
      (else
        (if (result i32) (i32.eqz (local.get $n))
          (then
            (call $ack (i32.sub (local.get $m) (i32.const 1)) (i32.const 1))
          )
          (else
            (call $ack
              (i32.sub (local.get $m) (i32.const 1))
              (call $ack (local.get $m) (i32.sub (local.get $n) (i32.const 1)))
            )
          )
        )
      )
    )
  )
)
"#;

const RUNS: usize = 5;

struct BenchResult {
    name: &'static str,
    ms: f64,
}

fn bench<F: FnMut() -> i32>(mut f: F) -> (i32, f64) {
    std::hint::black_box(f()); // warmup
    let mut total = 0.0;
    let mut result = 0i32;
    for _ in 0..RUNS {
        let t0 = Instant::now();
        result = f();
        total += t0.elapsed().as_secs_f64() * 1000.0;
    }
    (result, total / RUNS as f64)
}

fn print_table(results: &[BenchResult], jit_ms: f64, interp_ms: f64) {
    let name_w = results.iter().map(|r| r.name.len()).max().unwrap_or(10);

    println!(
        "  {:<name_w$}  {:>10}  {:>10}  {:>10}",
        "engine", "avg ms", "vs jit", "vs interp"
    );
    println!("  {}", "-".repeat(name_w + 36));

    for r in results {
        let vs_jit = if jit_ms > 0.001 && r.ms > 0.001 {
            format!("{:.2}x", r.ms / jit_ms)
        } else {
            "-".to_string()
        };
        let vs_interp = if interp_ms > 0.001 && r.ms > 0.001 {
            format!("{:.2}x", r.ms / interp_ms)
        } else {
            "-".to_string()
        };
        println!(
            "  {:<name_w$}  {:>10.3}  {:>10}  {:>10}",
            r.name, r.ms, vs_jit, vs_interp
        );
    }
}

fn main() {
    let m: i32 = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(3);
    let n: i32 = std::env::args()
        .nth(2)
        .and_then(|s| s.parse().ok())
        .unwrap_or(12);

    let wasm_bytes = wat::parse_str(ACK_WAT).expect("failed to parse WAT");

    // Setup wust interpreter.
    let engine = Engine::default();
    let module = Module::from_bytes(&engine, &wasm_bytes).expect("failed to parse module");
    let linker = Linker::new(&engine);
    let (mut interp_store, mut interp_instance) = {
        let mut store = Store::new(&engine, ());
        let instance = linker
            .instantiate(&mut store, &module)
            .expect("failed to instantiate");
        (store, instance)
    };

    // Setup wust JIT (with fuel).
    let jit_module = JitModule::compile(&module).expect("JIT compilation failed");
    let mut jit_instance = linker
        .instantiate(&mut Store::new(&engine, ()), &module)
        .expect("failed to instantiate for JIT");

    // Setup wust JIT (no fuel).
    let jit_no_fuel = JitCompiler::new(&module)
        .fuel(false)
        .compile()
        .expect("JIT no-fuel compilation failed");
    let mut jit_nf_instance = linker
        .instantiate(&mut Store::new(&engine, ()), &module)
        .expect("failed to instantiate for JIT no-fuel");

    // Setup wasmtime.
    let wt_engine = wasmtime::Engine::default();
    let wt_module =
        wasmtime::Module::new(&wt_engine, &wasm_bytes).expect("wasmtime compile failed");
    let mut wt_store = wasmtime::Store::new(&wt_engine, ());
    let wt_instance = wasmtime::Instance::new(&mut wt_store, &wt_module, &[])
        .expect("wasmtime instantiate failed");
    let wt_func = wt_instance
        .get_typed_func::<(i32, i32), i32>(&mut wt_store, "ack")
        .expect("wasmtime get_func failed");

    // Setup pulley.
    let mut pulley_config = wasmtime::Config::new();
    pulley_config
        .target("pulley64")
        .expect("failed to set pulley target");
    let pulley_engine =
        wasmtime::Engine::new(&pulley_config).expect("pulley engine creation failed");
    let pulley_module =
        wasmtime::Module::new(&pulley_engine, &wasm_bytes).expect("pulley compile failed");
    let mut pulley_store = wasmtime::Store::new(&pulley_engine, ());
    let pulley_instance = wasmtime::Instance::new(&mut pulley_store, &pulley_module, &[])
        .expect("pulley instantiate failed");
    let pulley_func = pulley_instance
        .get_typed_func::<(i32, i32), i32>(&mut pulley_store, "ack")
        .expect("pulley get_func failed");

    // Native reference.
    #[inline(never)]
    fn ack_native(m: i32, n: i32) -> i32 {
        if m == 0 {
            n + 1
        } else if n == 0 {
            ack_native(m - 1, 1)
        } else {
            ack_native(m - 1, ack_native(m, n - 1))
        }
    }

    // Compute expected result from native.
    let expected = ack_native(m, n);

    // Try interpreter (may fail with stack overflow for large inputs).
    let interp_ms = match interp_instance.call_dynamic(
        &mut interp_store,
        "ack",
        &[Val::I32(m), Val::I32(n)],
    ) {
        Ok(_r) => {
            let (_, ms) = bench(|| {
                let r = interp_instance
                    .call_dynamic(&mut interp_store, "ack", &[Val::I32(m), Val::I32(n)])
                    .unwrap();
                match r[0] {
                    Val::I32(v) => v,
                    _ => panic!("expected i32"),
                }
            });
            ms
        }
        Err(_) => {
            eprintln!("note: interpreter stack too small for ack({m}, {n}), skipping");
            0.0
        }
    };

    let run = |name: &'static str, mut f: Box<dyn FnMut() -> i32>| -> BenchResult {
        let (result, ms) = bench(|| f());
        assert_eq!(result, expected, "{name} result mismatch");
        BenchResult { name, ms }
    };

    let jit_result = run(
        "wust jit",
        Box::new(|| jit_module.call(&mut jit_instance, "ack", (m, n)).unwrap()),
    );
    let jit_ms = jit_result.ms;

    let jit_nf_result = run(
        "wust jit (no fuel)",
        Box::new(|| jit_no_fuel.call(&mut jit_nf_instance, "ack", (m, n)).unwrap()),
    );

    let results = vec![
        BenchResult {
            name: "wust interp",
            ms: interp_ms,
        },
        jit_result,
        jit_nf_result,
        run(
            "wasmtime",
            Box::new(|| wt_func.call(&mut wt_store, (m, n)).unwrap()),
        ),
        run(
            "pulley",
            Box::new(|| pulley_func.call(&mut pulley_store, (m, n)).unwrap()),
        ),
        run(
            "native",
            Box::new(|| ack_native(std::hint::black_box(m), std::hint::black_box(n))),
        ),
    ];

    println!("\nack({m}, {n}) = {expected}  (avg of {RUNS} runs)\n");
    print_table(&results, jit_ms, interp_ms);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ack() {
        let wasm_bytes = wat::parse_str(ACK_WAT).expect("failed to parse WAT");
        let engine = Engine::default();
        let module = Module::from_bytes(&engine, &wasm_bytes).expect("failed to parse module");
        let linker = Linker::new(&engine);
        let mut store = Store::new(&engine, ());
        let mut instance = linker
            .instantiate(&mut store, &module)
            .expect("failed to instantiate");
        let r = instance
            .call_dynamic(&mut store, "ack", &[Val::I32(3), Val::I32(4)])
            .expect("wust ack failed");
        match r[0] {
            Val::I32(v) => assert_eq!(v, 125),
            _ => panic!("expected i32"),
        }
    }
}
