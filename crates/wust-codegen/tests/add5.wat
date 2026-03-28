(module
  (func $add5 (export "add5") (param $a i32) (result i32)
    (i32.add (local.get $a) (i32.const 5))
  )
)
