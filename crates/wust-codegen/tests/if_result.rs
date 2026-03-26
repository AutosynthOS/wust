use autosynth_backend_aarch64::Aarch64Backend;
use wust_codegen::JitModule;

/// 5 + (if (0 == 0) then 10 else 20) = 15
///
/// Tests if-with-results: the if block produces a value that
/// gets consumed by i32.add. Uses i32.eqz so the condition
/// goes through Comp+BrIf fusion.
const WAT: &str = include_str!("if_result.wat");

#[test]
fn if_result_lower() -> anyhow::Result<()> {
    let bytes = wat::parse_str(WAT)?;
    let module = wust_core::ParsedModule::new(&bytes)?;
    let _jit = JitModule::<Aarch64Backend>::new(module)?;
    Ok(())
}

#[test]
fn if_result_jit() -> anyhow::Result<()> {
    use wust_core::exec::ModuleExecutor;

    let bytes = wat::parse_str(WAT)?;
    let module = wust_core::ParsedModule::new(&bytes)?;
    let instance = wust_core::Instance::new(&module);
    let jit = JitModule::<Aarch64Backend>::new(module.clone())?;

    let mut task = wust_core::Task::setup(&instance, "test", &[])?;
    task.context.fuel = i64::MAX;
    let outcome = jit.poll(&mut task);
    assert_eq!(outcome, wust_core::Outcome::Return);
    assert_eq!(task.results(), vec![wust_core::Val::I32(15)]); // 5 + 10
    Ok(())
}
