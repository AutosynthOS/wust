use super::*;
use crate::{Instance, ParsedModule, Val};

fn run(wat: &str, args: &[Val]) -> Vec<Val> {
    let wasm = wat::parse_str(wat).expect("bad WAT");
    let module = ParsedModule::new(&wasm).expect("parse failed");
    let instance = Instance::new(&module);
    let mut task = Task::setup(&instance, "f", args).expect("setup failed");
    let outcome = Interpreter.poll(&mut task);
    assert_eq!(outcome, Outcome::Return);
    task.results()
}

#[test]
fn return_i32_const() {
    let results = run(
        r#"(module (func (export "f") (result i32) i32.const 42))"#,
        &[],
    );
    assert_eq!(results, vec![Val::I32(42)]);
}

#[test]
fn return_i32_add() {
    let results = run(
        r#"(module (func (export "f") (result i32)
            i32.const 10
            i32.const 32
            i32.add
        ))"#,
        &[],
    );
    assert_eq!(results, vec![Val::I32(42)]);
}

#[test]
fn local_get_param() {
    let results = run(
        r#"(module (func (export "f") (param i32) (result i32)
            local.get 0
        ))"#,
        &[Val::I32(99)],
    );
    assert_eq!(results, vec![Val::I32(99)]);
}

#[test]
fn recursive_fib() {
    let results = run(
        r#"(module
            (func $fib (export "f") (param $n i32) (result i32)
                (if (i32.le_s (local.get $n) (i32.const 1))
                    (then (return (local.get $n)))
                )
                (i32.add
                    (call $fib (i32.sub (local.get $n) (i32.const 1)))
                    (call $fib (i32.sub (local.get $n) (i32.const 2)))
                )
            )
        )"#,
        &[Val::I32(10)],
    );
    assert_eq!(results, vec![Val::I32(55)]);
}

#[test]
fn bench_fib_30() {
    let wat = r#"(module
        (func $fib (export "f") (param $n i32) (result i32)
            (if (i32.le_s (local.get $n) (i32.const 1))
                (then (return (local.get $n)))
            )
            (i32.add
                (call $fib (i32.sub (local.get $n) (i32.const 1)))
                (call $fib (i32.sub (local.get $n) (i32.const 2)))
            )
        )
    )"#;
    let wasm = wat::parse_str(wat).expect("bad WAT");
    let module = ParsedModule::new(&wasm).expect("parse failed");
    let instance = Instance::new(&module);

    // Warmup
    for _ in 0..5 {
        let mut task = Task::setup(&instance, "f", &[Val::I32(30)]).expect("setup failed");
        Interpreter.poll(&mut task);
    }

    // Timed iterations
    let start = std::time::Instant::now();
    for _ in 0..10 {
        let mut task = Task::setup(&instance, "f", &[Val::I32(30)]).expect("setup failed");
        let outcome = Interpreter.poll(&mut task);
        assert_eq!(outcome, Outcome::Return);
        assert_eq!(task.results(), vec![Val::I32(832040)]);
    }
    let elapsed = start.elapsed();
    eprintln!(
        "fib(30) x10: {:.2}ms total, {:.2}ms/iter",
        elapsed.as_secs_f64() * 1000.0,
        elapsed.as_secs_f64() * 100.0,
    );
}
