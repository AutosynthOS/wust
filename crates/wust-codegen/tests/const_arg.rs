use autosynth_backend_aarch64::Aarch64Backend;
use wust_codegen::JitModule;

const WAT: &str = r#"
(module
  (func $f (export "f") (param $x i32) (result i32)
    (if (result i32) (i32.eqz (local.get $x))
      (then
        (i32.const 99)
      )
      (else
        (call $f (i32.const 0))
      )
    )
  )
)
"#;

#[test]
fn const_arg_lower() -> anyhow::Result<()> {
    let bytes = wat::parse_str(WAT)?;
    let module = wust_core::ParsedModule::new(&bytes)?;

    type Jit = JitModule<Aarch64Backend>;
    let _jit = Jit::new(module)?;
    Ok(())
}

#[test]
fn const_arg_jit() -> anyhow::Result<()> {
    use wust_core::exec::ModuleExecutor;

    let bytes = wat::parse_str(WAT)?;
    let module = wust_core::ParsedModule::new(&bytes)?;
    let instance = wust_core::Instance::new(&module);

    type Jit = JitModule<Aarch64Backend>;
    let jit = Jit::new(module.clone())?;

    // f(0) = 99 (base case, no call)
    let mut task = wust_core::Task::setup(&instance, "f", &[wust_core::Val::I32(0)])?;
    task.context.fuel = i64::MAX;
    let outcome = jit.poll(&mut task);
    assert_eq!(outcome, wust_core::Outcome::Return);
    assert_eq!(task.results(), vec![wust_core::Val::I32(99)]);

    // f(1) = 99 (calls f(0) with const arg 0)
    let mut task = wust_core::Task::setup(&instance, "f", &[wust_core::Val::I32(1)])?;
    task.context.fuel = i64::MAX;
    let outcome = jit.poll(&mut task);
    assert_eq!(outcome, wust_core::Outcome::Return);
    assert_eq!(task.results(), vec![wust_core::Val::I32(99)]);

    Ok(())
}
