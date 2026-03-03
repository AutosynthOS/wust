use wust::{Engine, Instance, JitModule, Module, Val};

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
    let mut instance = Instance::new()?;

    let results = jit.call_dynamic(&module, &mut instance, "answer", &[Val::I32(42)])?;
    assert_eq!(results, vec![Val::I32(142)]);

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
    let mut instance = Instance::new()?;

    let results = jit.call_dynamic(
        &module,
        &mut instance,
        "add3",
        &[Val::I32(10), Val::I32(20), Val::I32(30)],
    )?;
    assert_eq!(results, vec![Val::I32(60)]);

    Ok(())
}
