use std::time::Instant;
use wust::runtime::{Module, Store, Value};

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

fn main() {
    let n: i32 = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(30);

    let wasm_bytes = wat::parse_str(FIB_WAT).expect("failed to parse WAT");

    // ---- wust (our interpreter) ----
    let module = Module::from_bytes(&wasm_bytes).expect("failed to parse module");
    let mut store = Store::new(&module).expect("failed to instantiate module");

    // Warmup
    let _ = wust::runtime::exec::call(&module, &mut store, 0, &[Value::I32(10)]);

    let t0 = Instant::now();
    let result = wust::runtime::exec::call(&module, &mut store, 0, &[Value::I32(n)]);
    let wust_time = t0.elapsed();
    let wust_result = result.expect("wust fib failed")[0].unwrap_i32();

    // ---- wasmtime (JIT, in-process) ----
    let engine = wasmtime::Engine::default();
    let wt_module = wasmtime::Module::new(&engine, &wasm_bytes).expect("wasmtime compile failed");
    let mut wt_store = wasmtime::Store::new(&engine, ());
    let instance = wasmtime::Instance::new(&mut wt_store, &wt_module, &[])
        .expect("wasmtime instantiate failed");
    let fib_fn = instance
        .get_typed_func::<i32, i32>(&mut wt_store, "fib")
        .expect("wasmtime get_func failed");

    // Warmup
    let _ = fib_fn.call(&mut wt_store, 10);

    let t0 = Instant::now();
    let wasmtime_result = fib_fn.call(&mut wt_store, n).expect("wasmtime call failed");
    let wasmtime_time = t0.elapsed();

    assert_eq!(wust_result, wasmtime_result, "wasmtime result mismatch");

    // ---- native Rust (for reference) ----
    #[inline(never)]
    fn fib_native(n: i32) -> i32 {
        if n <= 1 {
            return n;
        }
        fib_native(n - 1) + fib_native(n - 2)
    }

    // Warmup
    std::hint::black_box(fib_native(std::hint::black_box(10)));

    let t0 = Instant::now();
    let native_result = fib_native(std::hint::black_box(n));
    let native_time = t0.elapsed();
    std::hint::black_box(native_result);

    assert_eq!(wust_result, native_result, "native result mismatch");

    // ---- Results ----
    println!("fib({n}) = {wust_result}\n");
    println!(
        "wust (interpreter):  {:>10.3} ms",
        wust_time.as_secs_f64() * 1000.0
    );
    println!(
        "wasmtime (JIT):      {:>10.3} ms",
        wasmtime_time.as_secs_f64() * 1000.0
    );
    println!(
        "native rust:         {:>10.3} ms",
        native_time.as_secs_f64() * 1000.0
    );
    println!();
    if native_time.as_nanos() > 0 {
        println!(
            "wust / native:       {:>7.1}x",
            wust_time.as_secs_f64() / native_time.as_secs_f64()
        );
        println!(
            "wasmtime / native:   {:>7.1}x",
            wasmtime_time.as_secs_f64() / native_time.as_secs_f64()
        );
        println!(
            "wust / wasmtime:     {:>7.1}x",
            wust_time.as_secs_f64() / wasmtime_time.as_secs_f64()
        );
    }
}
