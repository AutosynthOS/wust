#![feature(abi_custom)]

use autosynth_codegen::pipeline::compile;
use autosynth_ir::{AluOp, BlockId, CompOp, Operand, VCode};
use autosynth_isa::{PReg, UImm12};
use autosynth_select_aarch64::Aarch64Selector;

mod common;

/// WAT:
///   i32.const 5
///   local.get 0
///   i32.eqz           ;; param == 0 ?
///   if (result i32)
///     i32.const 10
///   else
///     i32.const 20
///   end
///   i32.add
///
/// Expected ASM (entry):
///   subs wzr, w0, #0   ;; compare param to 0
///   b.ne else           ;; branch if param != 0
///
/// Then: movz w1, #10; b merge
/// Else: movz w1, #20; b merge
/// Merge: add w0, w1, #5; ret
///
/// param == 0 → 5 + 10 = 15
/// param != 0 → 5 + 20 = 25
#[test]
fn if_result() {
    let module = common::parse_wat(include_str!("if_result.wat"));
    let func = common::compile_func(&module, 0);

    let mut selector = Aarch64Selector::new(func.alloc.clone());
    let result = compile(&func, &mut selector).unwrap();

    // 4 blocks: Entry, then(U4), else(U6), merge(U7)
    assert_eq!(result.block_order.len(), 4);

    // --- Entry ---
    // eqz fused into BrIf(Eq). param already in x0, zero folded to #0.
    // subs wzr, w0, #0 ; b.ne else
    common::assert_stream_eq(&result.blocks[&BlockId::Entry], &[
        Operand::PReg(PReg(0)).into(),    // param
        Operand::UImm12(UImm12::try_from(0).unwrap()).into(),
        VCode::BrIf { op: CompOp::Eq, block_if: BlockId::User(4), block_else: BlockId::User(6) },
    ]);

    // --- Then (U4) ---
    // Materialize 10 into x0 (param is dead, x0 is free), branch to merge.
    // movz w0, #10 ; b merge
    common::assert_stream_eq(&result.blocks[&BlockId::User(4)], &[
        Operand::Const(10).into(),
        VCode::Materialize,
        Operand::DstPReg(PReg(0)).into(),
        VCode::Branch { target: BlockId::User(7) },
    ]);

    // --- Else (U6) ---
    // Materialize 20 into x0 (same — param dead, x0 free), branch to merge.
    // movz w0, #20 ; b merge
    common::assert_stream_eq(&result.blocks[&BlockId::User(6)], &[
        Operand::Const(20).into(),
        VCode::Materialize,
        Operand::DstPReg(PReg(0)).into(),
        VCode::Branch { target: BlockId::User(7) },
    ]);

    // --- Merge (U7) ---
    // Phi in x0 (both predecessors materialized into x0).
    // add(phi, 5). Commutative swap: phi on lhs (x0), 5 folded to #5.
    // add w0, w0, #5 ; ret
    common::assert_stream_eq(&result.blocks[&BlockId::User(7)], &[
        Operand::PReg(PReg(0)).into(),    // phi
        Operand::UImm12(UImm12::try_from(5).unwrap()).into(),
        VCode::Alu { op: AluOp::Add },
        Operand::DstPReg(PReg(0)).into(),          // result → x0
        VCode::Return,
    ]);

    // Execute.
    let jit = common::jit_compile(&module, 0);
    assert_eq!(jit.call_i32(0), 15);   // param == 0 → then → 5 + 10
    assert_eq!(jit.call_i32(1), 25);   // param != 0 → else → 5 + 20
    assert_eq!(jit.call_i32(99), 25);
}
