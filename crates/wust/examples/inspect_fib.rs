use wust::{Codegen, Engine, Module};

const FIB_WAT: &str = r#"
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
"#;

fn main() -> anyhow::Result<()> {
    let engine = Engine::default();
    let module = Module::new(&engine, FIB_WAT)?;

    let output = Codegen::new(&module).compile()?;
    print!("{}", output.render_blocks());

    Ok(())
}
