use wust::{Engine, Instance, Module};

#[test]
fn return_const_i32() -> Result<(), anyhow::Error> {
    let engine = Engine::default();
    let module = Module::new(
        &engine,
        r#"
        (module
            (func (export "answer") (result i32)
                i32.const 42
            )
        )
    "#,
    )?;
    let mut instance = Instance::new()?;
    let result: (i32,) = wust::call(&module, &mut instance, "answer", ())?;
    assert_eq!(result, (42,));
    Ok(())
}

#[test]
fn multi_value_results_with_multiple_arguments() -> Result<(), anyhow::Error> {
    let engine = Engine::default();
    let module = Module::new(
        &engine,
        r#"
        (module
            (func (export "add") (param i32 i32) (result i32 i32)
                local.get 0
                local.get 1
                i32.add
                local.get 0
                local.get 1
                i32.add
            )
        )
    "#,
    )?;
    let mut instance = Instance::new()?;
    let result: (i32, i32) = wust::call(&module, &mut instance, "add", (0, 0))?;
    assert_eq!(result, (0, 0));
    Ok(())
}

#[test]
fn multi_value_results_with_carry() -> Result<(), anyhow::Error> {
    let engine = Engine::default();
    let module = Module::new(
        &engine,
        r#"
        (module
            (func (export "add_carry") (param i32 i32 i32) (result i32 i32 i32)
                local.get 0
                local.get 1
                local.get 2
            )
        )
    "#,
    )?;
    let mut instance = Instance::new()?;
    let result: (i32, i32, i32) = wust::call(&module, &mut instance, "add_carry", (0, 0, 0))?;
    assert_eq!(result, (0, 0, 0));
    Ok(())
}
