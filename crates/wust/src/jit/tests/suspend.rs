use wust_core::exec::ModuleExecutor;
use wust_core::exec::interp::Interpreter;
use wust_core::{FRAME_HEADER_SIZE, FuncIdx, Instance, Outcome, ParsedModule, Task, Val};

use crate::jit::JitModule;

fn parse(wat: &str) -> (ParsedModule, Instance) {
    let wasm = wat::parse_str(wat).expect("bad WAT");
    let module = ParsedModule::new(&wasm).expect("parse failed");
    let instance = Instance::new(&module);
    (module, instance)
}

const FIB_WAT: &str = r#"(module
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
)"#;

#[test]
fn jit_suspend_returns_suspended_outcome() {
    let (module, instance) = parse(FIB_WAT);
    let jit = JitModule::compile(&module).unwrap();
    let mut task = Task::setup(&instance, "fib", &[Val::I32(10)]).unwrap();
    task.context.fuel = 2;

    let outcome = jit.poll(&mut task);
    assert_eq!(outcome, Outcome::Suspended);
}

#[test]
fn jit_suspend_writes_resume_pc() {
    let (module, instance) = parse(FIB_WAT);
    let jit = JitModule::compile(&module).unwrap();
    let mut task = Task::setup(&instance, "fib", &[Val::I32(10)]).unwrap();
    task.context.fuel = 2;

    let outcome = jit.poll(&mut task);
    assert_eq!(outcome, Outcome::Suspended);

    let resume_pc = task.context.wasm_fp.frame().resume_pc;
    assert!(
        resume_pc > 0,
        "resume_pc should be set after suspend, got {resume_pc}"
    );
}

#[test]
fn interp_suspend_returns_suspended_outcome() {
    let (_module, instance) = parse(FIB_WAT);
    let mut task = Task::setup(&instance, "fib", &[Val::I32(10)]).unwrap();
    task.context.fuel = 2;

    let outcome = Interpreter.poll(&mut task);
    assert_eq!(outcome, Outcome::Suspended);
}

#[test]
fn interp_suspend_writes_resume_pc() {
    let (_module, instance) = parse(FIB_WAT);
    let mut task = Task::setup(&instance, "fib", &[Val::I32(10)]).unwrap();
    task.context.fuel = 2;

    let outcome = Interpreter.poll(&mut task);
    assert_eq!(outcome, Outcome::Suspended);

    let resume_pc = task.context.wasm_fp.frame().resume_pc;
    assert!(
        resume_pc > 0,
        "resume_pc should be set after suspend, got {resume_pc}"
    );
}

/// A single frame's debug snapshot.
#[derive(Debug, PartialEq)]
struct DebugFrame {
    func_idx: u32,
    resume_pc: u32,
    prev_fp_offset: u32,
    /// (local_index, value_bytes) — 4 bytes for i32, 8 for i64.
    locals: Vec<(usize, Vec<u8>)>,
    /// Raw operand stack slots (4 bytes each).
    operands: Vec<i32>,
}

/// Walk the frame chain from the current fp back to the root, returning
/// a list of `DebugFrame`s ordered outermost-first.
fn debug_frames(task: &Task) -> Vec<DebugFrame> {
    let module = &task.module;
    let base = task.context.wasm_fp.base();
    let mut fp = task.context.wasm_fp.ptr;
    let mut frames = Vec::new();

    loop {
        // Read header fields directly: [func_idx: u32 | resume_pc: u32 | prev_fp_offset: u32]
        let header_ptr = unsafe { fp.sub(FRAME_HEADER_SIZE) } as *const u32;
        let func_idx = unsafe { *header_ptr };
        let resume_pc = unsafe { *header_ptr.add(1) };
        let prev_fp_offset = unsafe { *header_ptr.add(2) };
        let func = &module.funcs[func_idx as usize];
        let operand_slots = func.body.operand_depth[resume_pc as usize] as usize;

        // Locals base is at fp - FRAME_HEADER_SIZE - locals_size
        let locals_base = unsafe { fp.sub(FRAME_HEADER_SIZE + func.locals_size as usize) };
        let all_types: Vec<_> = func.params.iter().chain(func.locals.iter()).collect();
        let mut locals = Vec::new();
        for (i, ty) in all_types.iter().enumerate() {
            let offset = func.local_byte_offsets[i] as usize;
            let size = match ty {
                wasmparser::ValType::I32 | wasmparser::ValType::F32 => 4,
                _ => 8,
            };
            let bytes =
                unsafe { std::slice::from_raw_parts(locals_base.add(offset), size).to_vec() };
            locals.push((i, bytes));
        }

        // Operands start at fp
        let mut operands = Vec::new();
        for s in 0..operand_slots {
            let val = unsafe { (fp.add(s * 4) as *const i32).read_unaligned() };
            operands.push(val);
        }

        frames.push(DebugFrame {
            func_idx,
            resume_pc,
            prev_fp_offset,
            locals,
            operands,
        });

        // Walk to parent frame
        if prev_fp_offset == 0 {
            break;
        }
        let parent_fp = unsafe { fp.sub(prev_fp_offset as usize) };
        if parent_fp <= base {
            break;
        }
        fp = parent_fp;
    }

    frames.reverse();
    frames
}

/// Run JIT with limited fuel on fib(10), read the suspend PC, then
/// step the interpreter to that same PC. Compare stack bytes.
#[test]
fn jit_and_interp_stacks_match_at_suspend() {
    let (module, instance) = parse(FIB_WAT);
    let jit = JitModule::compile(&module).unwrap();

    // 1. Run JIT — it suspends at its own safe point.
    let mut jit_task = Task::setup(&instance, "fib", &[Val::I32(10)]).unwrap();
    jit_task.context.fuel = 0;
    let jit_outcome = jit.poll(&mut jit_task);
    assert_eq!(jit_outcome, Outcome::Suspended);

    let target_pc = jit_task.context.wasm_fp.frame().resume_pc;
    assert!(target_pc > 0, "JIT should suspend at a non-zero PC");

    // The JIT's fp offset from base tells us how deep in the call stack
    // the suspend happened. We need the interpreter at the same depth
    // AND the same resume_pc on the current frame.
    let jit_fp_offset =
        jit_task.context.wasm_fp.ptr as usize - jit_task.context.wasm_fp.base() as usize;

    // 2. Step interpreter one instruction at a time until it reaches
    //    the same frame depth and resume_pc as the JIT.
    let mut interp_task = Task::setup(&instance, "fib", &[Val::I32(10)]).unwrap();
    let mut steps = 0u64;
    loop {
        interp_task.context.fuel = 1;
        let outcome = Interpreter.poll(&mut interp_task);
        steps += 1;

        let interp_fp_offset =
            interp_task.context.wasm_fp.ptr as usize - interp_task.context.wasm_fp.base() as usize;
        let interp_pc = interp_task.context.wasm_fp.frame().resume_pc;

        if interp_fp_offset == jit_fp_offset && interp_pc == target_pc {
            assert_eq!(outcome, Outcome::Suspended);
            break;
        }

        assert_eq!(
            outcome,
            Outcome::Suspended,
            "interpreter returned unexpectedly at pc={interp_pc} (step {steps})"
        );
        assert!(
            steps < 100_000,
            "interpreter did not converge after {steps} steps"
        );
    }

    // 3. Compare frames — they must be identical.
    let jit_frames = debug_frames(&jit_task);
    let interp_frames = debug_frames(&interp_task);

    if jit_frames != interp_frames {
        print_diff(&jit_frames, &interp_frames, &module);
        panic!("frame mismatch at resume_pc={target_pc}");
    }
}

/// Print two frame lists side-by-side, highlighting mismatches.
fn print_diff(jit: &[DebugFrame], interp: &[DebugFrame], module: &ParsedModule) {
    let max_len = jit.len().max(interp.len());

    let func_name = |idx: u32| -> String {
        module
            .exports
            .iter()
            .find(|(_, i)| **i == FuncIdx::new(idx))
            .map(|(name, _)| name.clone())
            .unwrap_or_else(|| format!("func_{idx}"))
    };

    eprintln!("\n╔══ [ FRAME DIFF ] ");

    if jit.len() != interp.len() {
        eprintln!(
            "║  frame count: JIT={} vs INTERP={} ✗",
            jit.len(),
            interp.len()
        );
    }

    for i in 0..max_len {
        eprintln!("╟── frame[{i}]");

        match (jit.get(i), interp.get(i)) {
            (Some(j), Some(ip)) => {
                let name = func_name(j.func_idx);
                let pc_mark = if j.resume_pc != ip.resume_pc {
                    " ✗"
                } else {
                    ""
                };
                eprintln!("║  func: {name}");
                eprintln!(
                    "║  pc:       {:>6}  │  {:<6}{pc_mark}",
                    j.resume_pc, ip.resume_pc
                );
                eprintln!(
                    "║  prev_fp:  {:>6}  │  {:<6}",
                    j.prev_fp_offset, ip.prev_fp_offset
                );

                let func = &module.funcs[j.func_idx as usize];
                let all_types: Vec<_> = func.params.iter().chain(func.locals.iter()).collect();

                let max_locals = j.locals.len().max(ip.locals.len());
                for li in 0..max_locals {
                    let kind = if li < func.params.len() {
                        "param"
                    } else {
                        "local"
                    };
                    let ty = format!("{:?}", all_types[li]).to_lowercase();
                    let jv = j
                        .locals
                        .get(li)
                        .map(|(_, b)| format_val(b))
                        .unwrap_or_default();
                    let iv = ip
                        .locals
                        .get(li)
                        .map(|(_, b)| format_val(b))
                        .unwrap_or_default();
                    let mark = if j.locals.get(li) != ip.locals.get(li) {
                        " ✗"
                    } else {
                        ""
                    };
                    eprintln!("║  {kind}[{li}]:  {:>6}  │  {:<6}  {ty}{mark}", jv, iv);
                }

                let max_ops = j.operands.len().max(ip.operands.len());
                for oi in 0..max_ops {
                    let jv = j
                        .operands
                        .get(oi)
                        .map(|v| v.to_string())
                        .unwrap_or("—".into());
                    let iv = ip
                        .operands
                        .get(oi)
                        .map(|v| v.to_string())
                        .unwrap_or("—".into());
                    let mark = if j.operands.get(oi) != ip.operands.get(oi) {
                        " ✗"
                    } else {
                        ""
                    };
                    eprintln!("║  op[{oi}]:    {:>6}  │  {:<6}{mark}", jv, iv);
                }
            }
            (Some(j), None) => {
                eprintln!("║  JIT only: {}  pc={}", func_name(j.func_idx), j.resume_pc);
            }
            (None, Some(ip)) => {
                eprintln!(
                    "║  INTERP only: {}  pc={}",
                    func_name(ip.func_idx),
                    ip.resume_pc
                );
            }
            (None, None) => unreachable!(),
        }
    }
    eprintln!("╚══════════════════════════════════════════════════\n");
}

fn format_val(bytes: &[u8]) -> String {
    if bytes.len() == 4 {
        i32::from_le_bytes(bytes[..4].try_into().unwrap()).to_string()
    } else {
        i64::from_le_bytes(bytes[..8].try_into().unwrap()).to_string()
    }
}
