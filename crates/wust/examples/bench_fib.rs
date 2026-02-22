use std::time::Instant;
use wust::{Engine, Linker, Module, Store, Val};

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

// Hand-compiled JIT variants (aarch64 assembly).
std::arch::global_asm!(include_str!("fib_jit.s"));

unsafe extern "C" {
    fn fib_jit_no_fuel(n: i32) -> i32;
    fn fib_jit_fuel_calls(n: i32, fuel: *mut i64) -> i32;
    fn fib_jit_fuel_all_entry(n: i32, fuel: i64) -> i32;
    fn fib_jit_fuel_eager_entry(n: i32, fuel: i64) -> i32;
    fn fib_jit_fuel_lazy_entry(n: i32, fuel: i64) -> i32;
    fn fib_jit_wasm_stack_entry(n: i32, fuel: i64, wasm_stack: *mut u8) -> i32;
    fn fib_jit_tailcall(n: i32) -> i32;
}

const RUNS: usize = 5;

/// A single benchmark entry: name + best-of-N time in ms.
struct BenchResult {
    name: &'static str,
    ms: f64,
}

/// Run a closure `RUNS` times, return (result, best time in ms).
fn bench<F: FnMut() -> i32>(mut f: F) -> (i32, f64) {
    std::hint::black_box(f()); // warmup
    let mut best = f64::MAX;
    let mut result = 0i32;
    for _ in 0..RUNS {
        let t0 = Instant::now();
        result = f();
        let elapsed = t0.elapsed().as_secs_f64() * 1000.0;
        best = best.min(elapsed);
    }
    (result, best)
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
    let instance = wasmtime::Instance::new(&mut store, &module, &[])
        .expect("wasmtime instantiate failed");
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
    let instance = wasmtime::Instance::new(&mut store, &module, &[])
        .expect("pulley instantiate failed");
    let func = instance
        .get_typed_func::<i32, i32>(&mut store, "fib")
        .expect("pulley get_func failed");
    (store, func)
}

fn print_table(results: &[BenchResult]) {
    // Column widths.
    let name_w = results.iter().map(|r| r.name.len()).max().unwrap_or(10);
    let ms_w = 10;
    let vs_w = 8;

    // Header row.
    print!("  {:<name_w$}  {:>ms_w$}", "engine", "ms");
    for r in results {
        print!("  {:>vs_w$}", r.name);
    }
    println!();

    // Separator.
    let total = name_w + 2 + ms_w + results.len() * (vs_w + 2) + 2;
    println!("  {}", "-".repeat(total));

    // Data rows.
    for row in results {
        print!("  {:<name_w$}  {:>ms_w$.3}", row.name, row.ms);
        for col in results {
            if col.ms < 0.001 || row.ms < 0.001 {
                print!("  {:>vs_w$}", "-");
            } else {
                print!("  {:>vs_w$.1}x", row.ms / col.ms);
            }
        }
        println!();
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

    #[inline(never)]
    fn fib_native(n: i32) -> i32 {
        if n <= 1 { return n; }
        fib_native(n - 1) + fib_native(n - 2)
    }

    // Run all benchmarks, collecting results.
    let (expected, wust_ms) = bench(|| {
        let r = wust_instance
            .call_dynamic(&mut wust_store, "fib", &[Val::I32(n)])
            .expect("wust fib failed");
        match r[0] { Val::I32(v) => v, _ => panic!("expected i32") }
    });

    let run = |name: &'static str, mut f: Box<dyn FnMut() -> i32>| -> BenchResult {
        let (result, ms) = bench(|| f());
        assert_eq!(result, expected, "{name} result mismatch");
        BenchResult { name, ms }
    };

    let results = vec![
        BenchResult { name: "wust interp", ms: wust_ms },
        run("pulley", Box::new(|| pulley_func.call(&mut pulley_store, n).unwrap())),
        run("wasmtime", Box::new(|| wt_func.call(&mut wt_store, n).unwrap())),
        run("native", Box::new(|| fib_native(std::hint::black_box(n)))),
        run("jit", Box::new(|| unsafe { fib_jit_no_fuel(std::hint::black_box(n)) })),
        run("jit+fuel@call", Box::new(|| unsafe {
            let mut fuel: i64 = i64::MAX;
            fib_jit_fuel_calls(std::hint::black_box(n), &mut fuel)
        })),
        run("jit+fuel@op", Box::new(|| unsafe {
            fib_jit_fuel_all_entry(std::hint::black_box(n), i64::MAX)
        })),
        run("jit+eager", Box::new(|| unsafe {
            fib_jit_fuel_eager_entry(std::hint::black_box(n), i64::MAX)
        })),
        run("jit+lazy", Box::new(|| unsafe {
            fib_jit_fuel_lazy_entry(std::hint::black_box(n), i64::MAX)
        })),
        run("jit+wasmstk", Box::new(|| unsafe {
            // 1MB wasm stack — plenty for fib(30)
            let mut wasm_stack = vec![0u8; 1024 * 1024];
            fib_jit_wasm_stack_entry(
                std::hint::black_box(n),
                i64::MAX,
                wasm_stack.as_mut_ptr(),
            )
        })),
        run("jit tailcall", Box::new(|| unsafe {
            fib_jit_tailcall(std::hint::black_box(n))
        })),
    ];

    println!("\nfib({n}) = {expected}  (best of {RUNS} runs)\n");
    print_table(&results);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fib() {
        let wasm_bytes = wat::parse_str(FIB_WAT).expect("failed to parse WAT");
        let (mut store, mut instance) = setup_wust(&wasm_bytes);
        let result = instance
            .call_dynamic(&mut store, "fib", &[Val::I32(30)])
            .expect("wust fib failed");
        assert_eq!(result[0], Val::I32(832040));
    }
}
