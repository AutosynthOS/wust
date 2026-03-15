use autosynth_backend_aarch64::Aarch64Backend;
use autosynth_codegen::{
    Align,
    debugger::{self, Debugger},
};
use wust_codegen::JitModule;

const WAT: &str = r#"
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

#[test]
fn ack_lower() -> anyhow::Result<()> {
    let bytes = wat::parse_str(WAT)?;
    let module = wust_core::ParsedModule::new(&bytes)?;

    let mut dbg = Debugger::new();
    dbg.add_machine_column("addr", Align::Right);
    dbg.add_machine_column("asm", Align::Left);
    debugger::install(dbg);

    type Jit = JitModule<Aarch64Backend>;
    let _jit = Jit::new(module)?;

    let dbg = debugger::take().unwrap();
    eprintln!("\n{}", dbg.render());
    Ok(())
}

#[test]
fn ack_jit() -> anyhow::Result<()> {
    use wust_core::exec::ModuleExecutor;

    let bytes = wat::parse_str(WAT)?;
    let module = wust_core::ParsedModule::new(&bytes)?;
    let instance = wust_core::Instance::new(&module);

    type Jit = JitModule<Aarch64Backend>;
    let jit = Jit::new(module.clone())?;

    // ack(0, 0) = 1
    let mut task = wust_core::Task::setup(&instance, "ack", &[wust_core::Val::I32(0), wust_core::Val::I32(0)])?;
    task.context.fuel = i64::MAX;
    let outcome = jit.poll(&mut task);
    assert_eq!(outcome, wust_core::Outcome::Return);
    assert_eq!(task.results(), vec![wust_core::Val::I32(1)]);

    // ack(1, 1) = 3
    let mut task = wust_core::Task::setup(&instance, "ack", &[wust_core::Val::I32(1), wust_core::Val::I32(1)])?;
    task.context.fuel = i64::MAX;
    let outcome = jit.poll(&mut task);
    assert_eq!(outcome, wust_core::Outcome::Return);
    assert_eq!(task.results(), vec![wust_core::Val::I32(3)]);

    // ack(2, 2) = 7
    let mut task = wust_core::Task::setup(&instance, "ack", &[wust_core::Val::I32(2), wust_core::Val::I32(2)])?;
    task.context.fuel = i64::MAX;
    let outcome = jit.poll(&mut task);
    assert_eq!(outcome, wust_core::Outcome::Return);
    assert_eq!(task.results(), vec![wust_core::Val::I32(7)]);

    Ok(())
}
