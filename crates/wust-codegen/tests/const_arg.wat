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
