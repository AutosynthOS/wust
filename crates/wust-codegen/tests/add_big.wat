(module
  (func $add_big (export "add_big") (param $a i32) (result i32)
    (i32.add (local.get $a) (i32.const 5000))
  )
)
