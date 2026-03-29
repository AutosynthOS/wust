#![feature(abi_custom)]

use autosynth_codegen::pipeline::compile;
use autosynth_ir::{AluOp, BlockId, FunctionIdx, Label, Operand, VCode};
use autosynth_isa::{PReg, UImm12, Width};
use autosynth_select_aarch64::Aarch64Selector;

mod common;

/// add5: (param i32) (result i32) = param + 5
///
/// Expected compiled output with prologue/epilogue:
///
/// Entry block (prologue):
///   sub sp, sp, #16         ;; allocate fibre stack
///   str x30, [sp]           ;; save lr
///   ldr w0, [x29, #0]       ;; load param from managed stack
///   bl body                 ;; call function body
///   str w0, [x29, #0]       ;; store result to managed stack
///   ldr x30, [sp]           ;; restore lr
///   add sp, sp, #16         ;; deallocate fibre stack
///   ret                     ;; return to host
///
/// Body block:
///   add w0, w0, #5
///   ret                     ;; return to prologue
#[test]
fn add5_vcode() {
    let module = common::parse_wat(include_str!("add5.wat"));
    let func = common::compile_func(&module, 0);

    let mut selector = Aarch64Selector::new(func.alloc.clone());
    let result = compile(&func, &mut selector).unwrap();

    // Body block — the actual computation.
    common::assert_stream_eq(&result.blocks[&BlockId::Entry], &[
        Operand::PReg(PReg(0)).into(),
        Operand::UImm12(UImm12::try_from(5).unwrap()).into(),
        VCode::Alu { op: AluOp::Add },
        Operand::DstPReg(PReg(0), Width::W32).into(),
        VCode::Return,
    ]);
}

/// Execution test — call through the trampoline.
#[test]
fn add5_exec() {
    let module = common::parse_wat(include_str!("add5.wat"));
    let jit = common::jit_compile(&module, 0);
    assert_eq!(jit.call_i32(10), 15);
    assert_eq!(jit.call_i32(0), 5);
    assert_eq!(jit.call_i32(100), 105);
}
