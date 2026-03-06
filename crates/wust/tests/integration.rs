use wust::{JitModule, ModuleExecutor, Outcome, Val};
use wust_core::{Instance, ParsedModule, Task};

fn parse(wat: &str) -> (ParsedModule, Instance) {
    let wasm = wat::parse_str(wat).expect("bad WAT");
    let module = ParsedModule::new(&wasm).expect("parse failed");
    let instance = Instance::new(&module);
    (module, instance)
}

#[test]
fn suspend_on_fuel_exhaustion() -> Result<(), anyhow::Error> {
    let (module, instance) = parse(
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
    );

    let jit = JitModule::compile(&module)?;
    let mut task = Task::setup(&instance, "fib", &[Val::I32(3)])?;
    task.context.fuel = 2;

    let outcome = jit.poll(&mut task);
    assert_eq!(outcome, Outcome::Suspended);

    Ok(())
}
