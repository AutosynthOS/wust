use wust::{Engine, ExecBackend, JitModule, Module, Outcome, Task, Val};

#[test]
fn call_add() -> Result<(), anyhow::Error> {
    let wasm = wat::parse_str(
        r#"
        (module
            (func $add (param $a i32) (param $b i32) (result i32)
                local.get $a
                local.get $b
                i32.add
            )
            (func (export "answer") (param $x i32) (result i32)
                local.get $x
                i32.const 100
                call $add
            )
        )
    "#,
    )?;

    let engine = Engine::default();
    let module = Module::from_bytes(&engine, &wasm)?;
    let jit = JitModule::compile(&module)?;
    let mut task = Task::new()?;

    wust::setup(&module, &mut task, "answer", &[Val::I32(42)])?;
    let outcome = jit.poll(&module, &mut task, i64::MAX);
    assert_eq!(outcome, Outcome::Return);
    assert_eq!(wust::results(&module, &task), vec![Val::I32(142)]);

    Ok(())
}

#[test]
fn call_multi_param() -> Result<(), anyhow::Error> {
    let wasm = wat::parse_str(
        r#"
        (module
            (func (export "add3") (param i32) (param i32) (param i32) (result i32)
                local.get 0
                local.get 1
                i32.add
                local.get 2
                i32.add
            )
        )
    "#,
    )?;

    let engine = Engine::default();
    let module = Module::from_bytes(&engine, &wasm)?;
    let jit = JitModule::compile(&module)?;
    let mut task = Task::new()?;

    wust::setup(
        &module,
        &mut task,
        "add3",
        &[Val::I32(10), Val::I32(20), Val::I32(30)],
    )?;
    let outcome = jit.poll(&module, &mut task, i64::MAX);
    assert_eq!(outcome, Outcome::Return);
    assert_eq!(wust::results(&module, &task), vec![Val::I32(60)]);

    Ok(())
}

#[test]
fn suspend_on_fuel_exhaustion() -> Result<(), anyhow::Error> {
    let wasm = wat::parse_str(
        r#"
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
    "#,
    )?;

    let engine = Engine::default();
    let module = Module::from_bytes(&engine, &wasm)?;
    let jit = JitModule::compile(&module)?;
    let mut task = Task::new()?;

    wust::setup(&module, &mut task, "fib", &[Val::I32(3)])?;
    let outcome = jit.poll(&module, &mut task, 0);
    assert_eq!(outcome, Outcome::Suspended);

    // The argument (n=3) should still be in its frame slot.
    let local_0 = task.stack.read_u64_at(16) as i32;
    assert_eq!(local_0, 3, "local 0 (n) should be 3 after suspend");

    Ok(())
}
