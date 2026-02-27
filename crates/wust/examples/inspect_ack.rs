use wust::{Codegen, Engine, Module};

const ACK_WAT: &str = r#"
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

fn main() -> anyhow::Result<()> {
    let engine = Engine::default();
    let module = Module::new(&engine, ACK_WAT)?;
    let output = Codegen::new(&module).compile()?;
    print!("{}", output.render_blocks());
    Ok(())
}
