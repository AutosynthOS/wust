use std::io::Write;
use wust::{Engine, JitCompiler, Module};

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

fn main() {
    let path = std::env::args().nth(1).unwrap_or_else(|| "/tmp/wust_code.bin".into());
    let engine = Engine::default();
    let wasm_bytes = wat::parse_str(FIB_WAT).unwrap();
    let module = Module::from_bytes(&engine, &wasm_bytes).expect("parse");
    let jit = JitCompiler::new(&module).compile().expect("compile");
    let code = jit.code_bytes();
    let mut f = std::fs::File::create(&path).expect("create");
    f.write_all(code).expect("write");
    eprintln!("wrote {} bytes to {}", code.len(), path);
}
