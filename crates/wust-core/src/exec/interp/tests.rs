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
