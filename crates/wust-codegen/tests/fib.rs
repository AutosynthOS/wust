const WAT: &str = r#"
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

// fn fib<0>(w9<i32>) -> w9<i32>
// 0000 │  str   g.lr, [g.sp, #-16]!            prologue
// 0004 │  movz  x10, #0x0, lsl #0x0
// 0008 │  subs  wzr, w9, #0x1                  sub(local.get 0, 1)
// 000c ├─╮ b.gt  L0
// 0010 │ │  sub   g.fuel, g.fuel, #0x3
// 0014 │ │  add   g.sp, g.sp, #0x10            sub(local.get 0, 2)
// 0018 │ │  ret   g.lr                         → w9<i32>
//      │ ╰─ end
// 001c │  sub   w12, w9, #0x1
// 0020 │  str   w9, [g.lb]
// 0024 │  subs  g.fuel, g.fuel, #0x2           fuel consume
// 0028 ├─╮ b.le  suspend                       fuel check
// 0074 │ │  movz  w0, #0x0, lsl #0x0           suspend: func_idx = 0
// 0078 │ │  str   w0, [g.lb, #0xc]             suspend: func_idx = 0
// 007c │ │  movz  w0, #0xb, lsl #0x0           resume_pc = 11
// 0080 │ │  str   w0, [g.lb, #0x10]            resume_pc = 11
// 0084 │ │  ldr   g.lr, [g.sp], #16
// 0088 │ │  ret   g.lr
//      │ ╰─ end
// 002c │  orr   w9, wzr, w12
// 0030 │  add   g.lb, g.lb, #0x18
// 0034 │  bl    fib<0>(w9<i32>) -> w9<i32>
// 0038 │  sub   g.lb, g.lb, #0x18
// 003c │  ldr   w10, [g.lb]
// 0040 │  orr   w11, wzr, w9
// 0044 │  sub   w9, w10, #0x2
// 0048 │  str   w11, [g.lb, #0x4]
// 004c │  subs  g.fuel, g.fuel, #0x2           fuel consume
// 0050 ├─╮ b.le  suspend                       fuel check
// 008c │ │  movz  w0, #0x0, lsl #0x0           suspend: func_idx = 0
// 0090 │ │  str   w0, [g.lb, #0xc]             suspend: func_idx = 0
// 0094 │ │  movz  w0, #0x10, lsl #0x0          resume_pc = 16
// 0098 │ │  str   w0, [g.lb, #0x10]            resume_pc = 16
// 009c │ │  movz  w0, #0x18, lsl #0x0          callee prev_fp_offset = 24
// 00a0 │ │  str   w0, [g.lb, #0x2c]            callee prev_fp_offset = 24
// 00a4 │ │  ldr   g.lr, [g.sp], #16
// 00a8 │ │  ret   g.lr
//      │ ╰─ end
// 0054 │  add   g.lb, g.lb, #0x18
// 0058 │  bl    fib<0>(w9<i32>) -> w9<i32>
// 005c │  sub   g.lb, g.lb, #0x18
// 0060 │  ldr   w10, [g.lb, #0x4]
// 0064 │  add   w9, w10, w9
// 0068 │  sub   g.fuel, g.fuel, #0x1
// 006c │  ldr   g.lr, [g.sp], #16
// 0070 │  ret   g.lr                           → w9<i32>
//      ╰─ end

#[test]
fn fib_ir_dump() -> anyhow::Result<()> {
    use autosynth_codegen::ir::instruction::IrInst;

    let bytes = wat::parse_str(WAT)?;
    let module = wust_core::ParsedModule::new(&bytes)?;
    let jit = wust_codegen::JitModule::new(module)?;
    let ir = jit.ir();

    for (i, func) in ir.functions().iter().enumerate() {
        eprintln!("=== function {i} ===");
        for block in &func.blocks {
            eprintln!("\n  {:?}:", block.id);
            eprintln!("    params:     {:?}", block.params);
            eprintln!("    successors: {:?}", block.successors);
            for inst in &block.instructions {
                match inst {
                    IrInst::StackPush { def } =>
                        eprintln!("    push {:?}({:?}) = {:?}", def.id, def.ty, def.value),
                    IrInst::StackPop { def } =>
                        eprintln!("    pop  {:?}({:?})", def.id, def.ty),
                    IrInst::Alu { op, dst, lhs, rhs } =>
                        eprintln!("    {dst:?} = {op:?} {lhs:?}, {rhs:?}"),
                    IrInst::Cmp { op, dst, lhs, rhs } =>
                        eprintln!("    {dst:?} = {op:?} {lhs:?}, {rhs:?}"),
                    IrInst::BrIf { cond, block_if, block_else } =>
                        eprintln!("    brif {cond:?} → {block_if:?} / {block_else:?}"),
                    IrInst::Branch { target } =>
                        eprintln!("    br {target:?}"),
                    IrInst::Call { func_idx } =>
                        eprintln!("    call {func_idx:?}"),
                    IrInst::Return { values } =>
                        eprintln!("    return {values:?}"),
                }
            }
            eprintln!("    results:    {:?}", block.results);
        }
    }
    Ok(())
}

#[test]
fn fib_jit() -> anyhow::Result<()> {
    use wust_core::exec::ModuleExecutor;

    let bytes = wat::parse_str(WAT)?;
    let module = wust_core::ParsedModule::new(&bytes)?;
    let instance = wust_core::Instance::new(&module);

    let jit = wust_codegen::JitModule::new(module.clone())?;
    let mut task = wust_core::Task::setup(&instance, "fib", &[wust_core::Val::I32(10)])?;
    task.context.fuel = i64::MAX;

    let outcome = jit.poll(&mut task);
    assert_eq!(outcome, wust_core::Outcome::Return);

    let results = task.results();
    assert_eq!(results, vec![wust_core::Val::I32(55)]);

    Ok(())
}
