use std::time::Instant;
use wust::{Engine, JitCompiler, JitModule, Linker, Module, Store, Val};

const FIB_WAT: &str = r#"
(module
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
)
"#;

// Hand-written aarch64 reference implementations.
std::arch::global_asm!(include_str!("fib_jit.s"));

unsafe extern "C" {
    fn fib_asm_no_fuel(n: i32) -> i32;
    fn fib_asm_fuel_calls(n: i32, fuel: *mut i64) -> i32;
    fn fib_asm_fuel_all_entry(n: i32, fuel: i64) -> i32;
    fn fib_asm_jumptable_entry(n: i32, fuel: i64) -> i32;
    fn fib_asm_wasm_stack_entry(n: i32, fuel: i64, wasm_stack: *mut u8) -> i32;
    fn fib_jit_reload_entry(n: i32, fuel: i64) -> i32;
    fn fib_jit_norld_entry(n: i32, fuel: i64) -> i32;
}

const RUNS: usize = 5;

struct BenchResult {
    name: &'static str,
    ms: f64,
}

/// Run a closure `RUNS` times, return (result, average time in ms).
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

fn setup_wust(wasm_bytes: &[u8]) -> (Store<()>, wust::Instance) {
    let engine = Engine::default();
    let mut store = Store::new(&engine, ());
    let module = Module::from_bytes(&engine, wasm_bytes).expect("failed to parse module");
    let linker = Linker::new(&engine);
    let instance = linker
        .instantiate(&mut store, &module)
        .expect("failed to instantiate");
    (store, instance)
}

fn setup_wasmtime(wasm_bytes: &[u8]) -> (wasmtime::Store<()>, wasmtime::TypedFunc<i32, i32>) {
    let engine = wasmtime::Engine::default();
    let module = wasmtime::Module::new(&engine, wasm_bytes).expect("wasmtime compile failed");
    let mut store = wasmtime::Store::new(&engine, ());
    let instance =
        wasmtime::Instance::new(&mut store, &module, &[]).expect("wasmtime instantiate failed");
    let func = instance
        .get_typed_func::<i32, i32>(&mut store, "fib")
        .expect("wasmtime get_func failed");
    (store, func)
}

fn setup_pulley(wasm_bytes: &[u8]) -> (wasmtime::Store<()>, wasmtime::TypedFunc<i32, i32>) {
    let mut config = wasmtime::Config::new();
    config
        .target("pulley64")
        .expect("failed to set pulley target");
    let engine = wasmtime::Engine::new(&config).expect("pulley engine creation failed");
    let module = wasmtime::Module::new(&engine, wasm_bytes).expect("pulley compile failed");
    let mut store = wasmtime::Store::new(&engine, ());
    let instance =
        wasmtime::Instance::new(&mut store, &module, &[]).expect("pulley instantiate failed");
    let func = instance
        .get_typed_func::<i32, i32>(&mut store, "fib")
        .expect("pulley get_func failed");
    (store, func)
}

fn print_table(results: &[BenchResult], jit_ms: f64, interp_ms: f64) {
    let name_w = results.iter().map(|r| r.name.len()).max().unwrap_or(10);

    // Header
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
    let n: i32 = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(30);

    let wasm_bytes = wat::parse_str(FIB_WAT).expect("failed to parse WAT");

    // Setup all engines.
    let (mut wust_store, mut wust_instance) = setup_wust(&wasm_bytes);
    let (mut wt_store, wt_func) = setup_wasmtime(&wasm_bytes);
    let (mut pulley_store, pulley_func) = setup_pulley(&wasm_bytes);

    // JIT compile with wust (with fuel).
    let engine = Engine::default();
    let module = Module::from_bytes(&engine, &wasm_bytes).expect("failed to parse module");
    let jit_module = JitModule::compile(&module).expect("JIT compilation failed");
    let linker = Linker::new(&engine);
    let mut jit_instance = linker
        .instantiate(&mut Store::new(&engine, ()), &module)
        .expect("failed to instantiate for JIT");

    // JIT compile without fuel.
    let jit_no_fuel = JitCompiler::new(&module)
        .fuel(false)
        .compile()
        .expect("JIT no-fuel compilation failed");
    let mut jit_nf_instance = linker
        .instantiate(&mut Store::new(&engine, ()), &module)
        .expect("failed to instantiate for JIT no-fuel");

    #[inline(never)]
    fn fib_native(n: i32) -> i32 {
        if n <= 1 {
            return n;
        }
        fib_native(n - 1) + fib_native(n - 2)
    }

    // Run all benchmarks.
    let (expected, interp_ms) = bench(|| {
        let r = wust_instance
            .call_dynamic(&mut wust_store, "fib", &[Val::I32(n)])
            .expect("wust fib failed");
        match r[0] {
            Val::I32(v) => v,
            _ => panic!("expected i32"),
        }
    });

    let run = |name: &'static str, mut f: Box<dyn FnMut() -> i32>| -> BenchResult {
        let (result, ms) = bench(|| f());
        assert_eq!(result, expected, "{name} result mismatch");
        BenchResult { name, ms }
    };

    let jit_result = run(
        "wust jit",
        Box::new(|| jit_module.call(&mut jit_instance, "fib", (n,)).unwrap()),
    );
    let jit_ms = jit_result.ms;

    let jit_nf_result = run(
        "wust jit (no fuel)",
        Box::new(|| jit_no_fuel.call(&mut jit_nf_instance, "fib", (n,)).unwrap()),
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
            Box::new(|| wt_func.call(&mut wt_store, n).unwrap()),
        ),
        run(
            "pulley",
            Box::new(|| pulley_func.call(&mut pulley_store, n).unwrap()),
        ),
        run("native", Box::new(|| fib_native(std::hint::black_box(n)))),
        run(
            "asm",
            Box::new(|| unsafe { fib_asm_no_fuel(std::hint::black_box(n)) }),
        ),
        run(
            "asm+fuel@call",
            Box::new(|| unsafe {
                let mut fuel: i64 = i64::MAX;
                fib_asm_fuel_calls(std::hint::black_box(n), &mut fuel)
            }),
        ),
        run(
            "asm+fuel@op",
            Box::new(|| unsafe {
                fib_asm_fuel_all_entry(std::hint::black_box(n), i64::MAX)
            }),
        ),
        run(
            "asm+fuel+jmptbl",
            Box::new(|| unsafe {
                fib_asm_jumptable_entry(std::hint::black_box(n), i64::MAX)
            }),
        ),
        run(
            "asm+wasmstk",
            Box::new(|| unsafe {
                let mut wasm_stack = vec![0u8; 1024 * 1024];
                fib_asm_wasm_stack_entry(
                    std::hint::black_box(n),
                    i64::MAX,
                    wasm_stack.as_mut_ptr(),
                )
            }),
        ),
        run(
            "jit-style+reload",
            Box::new(|| unsafe {
                fib_jit_reload_entry(std::hint::black_box(n), i64::MAX)
            }),
        ),
        run(
            "jit-style+norld",
            Box::new(|| unsafe {
                fib_jit_norld_entry(std::hint::black_box(n), i64::MAX)
            }),
        ),
    ];

    println!("\nfib({n}) = {expected}  (avg of {RUNS} runs)\n");
    print_table(&results, jit_ms, interp_ms);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fib() {
        let wasm_bytes = wat::parse_str(FIB_WAT).expect("failed to parse WAT");
        let (mut store, mut instance) = setup_wust(&wasm_bytes);
        let (result,): (i32,) = instance
            .call(&mut store, "fib", (30,))
            .expect("wust fib failed");
        assert_eq!(result, 832040);
    }
}
