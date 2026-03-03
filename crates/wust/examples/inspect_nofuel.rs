use wust::{Codegen};
use wust_core::ParsedModule;

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
    let wasm_bytes = wat::parse_str(FIB_WAT)?;
    let module = ParsedModule::new(&wasm_bytes)?;
    let output = Codegen::new(&module).fuel(false).compile()?;
    print!("{}", output.render_blocks());
    Ok(())
}
