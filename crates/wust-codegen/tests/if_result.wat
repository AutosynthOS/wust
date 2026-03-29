(module
  ;; if (param == 0) then 10 else 20, add 5
  (func $test (export "test") (param i32) (result i32)
    i32.const 5
    local.get 0
    i32.eqz
    if (result i32)
      i32.const 10
    else
      i32.const 20
    end
    i32.add
  )
)
