#![feature(abi_custom)]

use autosynth_codegen::pipeline::compile;
use autosynth_ir::{AluOp, BlockId, FunctionIdx, Label, Operand, VCode};
use autosynth_isa::{PReg, UImm12, Width};
use autosynth_select_aarch64::Aarch64Selector;

mod common;

/// add5: (param i32) (result i32) = param + 5
///
/// Entry(0) — host trampoline:
///   sub sp, sp, #16         ;; allocate fibre frame
///   str x30, [sp]           ;; save host lr
///   ldr w0, [x29, #0]       ;; load param from managed stack
///   bl Entry(1)             ;; call body
///   str w0, [x29, #0]       ;; store result to managed stack
///   ldr x30, [sp]           ;; restore host lr
///   add sp, sp, #16         ;; deallocate fibre frame
///   ret                     ;; return to host
///
/// Entry(1) — body:
///   add w0, w0, #5
///   ret                     ;; return to trampoline

#[test]
fn add5_entry0_trampoline() {
    let module = common::parse_wat(include_str!("add5.wat"));
    let func = common::compile_func(&module, 0);

    let mut selector = Aarch64Selector::new(func.alloc.clone());
    let result = compile(&func, &mut selector).unwrap();

    // Entry(0) — trampoline: load param, call body, store result, return.
    common::assert_stream_eq(&result.blocks[&BlockId::Entry(0)], &[
        // sub sp, sp, #16 (allocate fibre frame)
        Operand::PReg(PReg(31)).into(),               // sp
        Operand::UImm12(UImm12::try_from(16).unwrap()).into(),
        VCode::Alu { op: AluOp::Sub },
        Operand::DstPReg(PReg(31), Width::W64).into(),
        // str x30, [sp] (save lr)
        Operand::PReg(PReg(30)).into(),               // lr value
        VCode::Store { offset: 0, width: Width::W64 },
        // ldr w0, [x29, #0] (load param from managed stack)
        VCode::Load { offset: 0, width: Width::W32 },
        Operand::DstPReg(PReg(0), Width::W32).into(),
        // bl Entry(1) (call body)
        VCode::Bl { target: Label::Block(FunctionIdx::User(0), BlockId::Entry(1)) },
        // str w0, [x29, #0] (store result to managed stack)
        Operand::PReg(PReg(0)).into(),
        VCode::Store { offset: 0, width: Width::W32 },
        // ldr x30, [sp] (restore lr)
        VCode::Load { offset: 0, width: Width::W64 },
        Operand::DstPReg(PReg(30), Width::W64).into(),
        // add sp, sp, #16 (deallocate fibre frame)
        Operand::PReg(PReg(31)).into(),
        Operand::UImm12(UImm12::try_from(16).unwrap()).into(),
        VCode::Alu { op: AluOp::Add },
        Operand::DstPReg(PReg(31), Width::W64).into(),
        // ret to host
        VCode::Return,
    ]);
}

#[test]
fn add5_entry1_body() {
    let module = common::parse_wat(include_str!("add5.wat"));
    let func = common::compile_func(&module, 0);

    let mut selector = Aarch64Selector::new(func.alloc.clone());
    let result = compile(&func, &mut selector).unwrap();

    // Entry(1) — body: add param + 5, return.
    common::assert_stream_eq(&result.blocks[&BlockId::Entry(1)], &[
        Operand::PReg(PReg(0)).into(),
        Operand::UImm12(UImm12::try_from(5).unwrap()).into(),
        VCode::Alu { op: AluOp::Add },
        Operand::DstPReg(PReg(0), Width::W32).into(),
        VCode::Return,
    ]);
}

#[test]
fn add5_exec() {
    let module = common::parse_wat(include_str!("add5.wat"));
    let jit = common::jit_compile(&module, 0);
    assert_eq!(jit.call_i32(10), 15);
    assert_eq!(jit.call_i32(0), 5);
    assert_eq!(jit.call_i32(100), 105);
}
