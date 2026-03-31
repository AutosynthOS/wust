#![feature(abi_custom)]

use autosynth_codegen::pipeline::compile;
use autosynth_ir::{AluOp, BlockId, FunctionIdx, Label, Operand, VCode};
use autosynth_isa::{PReg, SImm9, UImm12, Width};
use autosynth_select_aarch64::Aarch64Selector;

mod common;

/// add5: (param i32) (result i32) = param + 5
///
/// Entry(0) — host trampoline:
///   str x30, [sp, #-16]!    ;; save lr, sp -= 16
///   ldr w0, [x29, #0]       ;; load param from managed stack
///   bl Entry(1)             ;; call body
///   str w0, [x29, #0]       ;; store result to managed stack
///   ldr x30, [sp], #16      ;; restore lr, sp += 16
///   ret                     ;; return to host
///
/// Entry(1) — body:
///   add w0, w0, #5
///   ret                     ;; return to trampoline
#[test]
fn add5() {
    let module = common::parse_wat(include_str!("add5.wat"));
    let func = common::compile_func(&module, 0);

    let mut selector = Aarch64Selector::new(func.alloc.clone());
    let result = compile(&func, &mut selector).unwrap();

    // Entry(0) — trampoline
    common::assert_stream_eq(
        &result.blocks[&BlockId::Entry(0)],
        &[
            // ldr w0, [x29, #0]
            Operand::PReg(PReg(29)).into(),
            Operand::UImm12(UImm12::try_from(0).unwrap()).into(),
            VCode::Load,
            Operand::DstPReg(PReg(0), Width::W32).into(),
            // str x30, [sp, #-16]!
            Operand::PReg(PReg(31)).into(),
            Operand::UImm12(UImm12::try_from(16).unwrap()).into(),
            VCode::Alu { op: AluOp::Sub },
            Operand::DstPReg(PReg(31), Width::W64).into(),
            // bl Entry(1)
            VCode::Bl {
                target: Label::Block(FunctionIdx::User(0), BlockId::Entry(1)),
            },
            // str w0, [x29, #0]
            Operand::PReg(PReg(0)).into(),
            Operand::PReg(PReg(29)).into(),
            Operand::UImm12(UImm12::try_from(0).unwrap()).into(),
            VCode::Store,
            // ldr x30, [sp], #16
            Operand::PReg(PReg(31)).into(),
            Operand::SImm9(SImm9::try_from(16).unwrap()).into(),
            VCode::Store,
            Operand::DstPReg(PReg(30), Width::W64).into(),
            // ret
            VCode::Return,
        ],
    );

    // Entry(1) — body
    common::assert_stream_eq(
        &result.blocks[&BlockId::Entry(1)],
        &[
            Operand::PReg(PReg(0)).into(),
            Operand::UImm12(UImm12::try_from(5).unwrap()).into(),
            VCode::Alu { op: AluOp::Add },
            Operand::DstPReg(PReg(0), Width::W32).into(),
            VCode::Return,
        ],
    );

    // Execute
    let jit = common::jit_compile(&module, 0);
    assert_eq!(jit.call_i32(10), 15);
    assert_eq!(jit.call_i32(0), 5);
    assert_eq!(jit.call_i32(100), 105);
}
