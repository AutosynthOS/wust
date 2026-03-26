(module
  (func $test (export "test") (result i32)
    i32.const 5
    i32.const 0
    i32.eqz
    if (result i32)
      i32.const 10
    else
      i32.const 20
    end
    i32.add
  )
)
