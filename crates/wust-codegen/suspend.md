```wat
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
```

### Rust-ish pseudocode

```rust
fn fib(n: i32) -> i32 {
    if n <= 1 {
        return n;
    }
    let a = fib(n - 1);
    let b = fib(n - 2);
    a + b
}
```

```asm

fn fib(local.n: i32) -> i32 {
    let local.a = i32.const:0
    let local.b = i32.const:0
    // before we call, we need to save our locals that were written to.
    stack[g.fp + 1] = local.n
    stack[g.fp + 2] = local.a
    stack[g.fp + 3] = local.b
    
    let v0 = i32.const:1
    let v1 = i32.le_s(n, consume:v0)
    br.not_zero(consume:v1) {
        return local.n
    }
    
    suspending:0 { // only executed when fuel is out
        stack[g.fp] = 0 // resume point
        ret
    }
        
    resume:0 { // only executed in resume mode
        local.n = stack[g.fp + 1]
        local.a = stack[g.fp + 2]
        local.b = stack[g.fp + 3]
        if g.rp != 0 {
           jump resume:1
        }
    }
    
    let v1 = i32.const:1
    let v2 = i32.sub(n, consume:v1)
    local.a = call fib(consume:v2->local.n)
    
    stack[g.fp + 2] = local.a
    suspending:1 {
        stack[g.fp] = 1 // resume point
        ret
    }
    
    resume:1 {
        if g.rp != 1 {
            jump resume:2
        }
    }
    
    let v3 = 2i32
    let v4 = i32.sub(n, consume:v3)
    local.b = call fib(consume:v4->local.n)
    
    stack[g.fp + 3] = local.b
    suspending:2 {
        stack[g.fp] = 2 // resume point
        ret
    }
    
    resume:2 {
        // already loaded everything
    }
    
    i32.add(local.a, local.b)
    return
}

```
