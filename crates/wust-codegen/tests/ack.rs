use autosynth_backend_aarch64::Aarch64Backend;
use wust_codegen::JitModule;

const WAT: &str = include_str!("ack.wat");

#[test]
fn ack_lower() -> anyhow::Result<()> {
    let bytes = wat::parse_str(WAT)?;
    let module = wust_core::ParsedModule::new(&bytes)?;

    type Jit = JitModule<Aarch64Backend>;
    let _jit = Jit::new(module)?;
    Ok(())
}

#[test]
fn ack_jit_small() -> anyhow::Result<()> {
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

    // ack(1, 0) = 2
    let mut task = wust_core::Task::setup(&instance, "ack", &[wust_core::Val::I32(1), wust_core::Val::I32(0)])?;
    task.context.fuel = i64::MAX;
    let outcome = jit.poll(&mut task);
    assert_eq!(outcome, wust_core::Outcome::Return);
    assert_eq!(task.results(), vec![wust_core::Val::I32(2)]);

    Ok(())
}

#[test]
#[ignore] // slow — deeply recursive
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
