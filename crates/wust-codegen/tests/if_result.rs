#![feature(abi_custom)]

use autosynth_codegen::pipeline::compile;
use autosynth_ir::{AluOp, BlockId, CompOp, Operand, VCode};
use autosynth_isa::{PReg, UImm12};
use autosynth_select_aarch64::Aarch64Selector;

mod common;

/// WAT:
///   i32.const 5
///   local.get 0
///   i32.eqz
///   if (result i32)
///     i32.const 10
///   else
///     i32.const 20
///   end
///   i32.add
///
/// if param == 0: result = 5 + 10 = 15
/// if param != 0: result = 5 + 20 = 25
#[test]
fn if_result() {
    let module = common::parse_wat(include_str!("if_result.wat"));
    let func = common::compile_func(&module, 0);

    let mut selector = Aarch64Selector::new(func.alloc.clone());
    let result = compile(&func, &mut selector).unwrap();

    // 4 blocks: Entry, then(U4), else(U7), merge(U8)
    assert_eq!(result.block_order.len(), 4);

    // --- Entry block ---
    // eqz on param (x0) → cbz x0, then_block
    // No materialization needed — param is already in x0.
    common::assert_stream_eq(&result.blocks[&BlockId::Entry], &[
        Operand::PReg(PReg(0)).into(),    // param
        Operand::UImm12(UImm12::try_from(0).unwrap()).into(),
        VCode::BrIf { op: CompOp::Eq, block_if: BlockId::User(5), block_else: BlockId::User(8) },
    ]);

    // --- Then block ---
    // Convergence materializes Const(10) for the phi → x1.
    common::assert_stream_eq(&result.blocks[&BlockId::User(5)], &[
        Operand::Const(10).into(),
        VCode::Materialize,
        VCode::Branch { target: BlockId::User(9) },
    ]);

    // --- Else block ---
    // Convergence materializes Const(20) for the phi → x1.
    common::assert_stream_eq(&result.blocks[&BlockId::User(8)], &[
        Operand::Const(20).into(),
        VCode::Materialize,
        VCode::Branch { target: BlockId::User(9) },
    ]);

    // --- Merge block ---
    // add(5, phi). Const(5) on lhs, phi on rhs.
    // Commutative swap: phi becomes lhs, 5 folds to #5 on rhs.
    common::assert_stream_eq(&result.blocks[&BlockId::User(9)], &[
        Operand::PReg(PReg(1)).into(),    // phi
        Operand::UImm12(UImm12::try_from(5).unwrap()).into(), // Const(5) folded
        VCode::Alu { op: AluOp::Add },
        VCode::DstPReg(PReg(0)),          // result → x0 (return register)
        VCode::Return,
    ]);

    // Execute.
    let jit = common::jit_compile(&module, 0);
    assert_eq!(jit.call_i32(0), 15);   // 0 == 0 → then → 5 + 10
    assert_eq!(jit.call_i32(1), 25);   // 1 != 0 → else → 5 + 20
    assert_eq!(jit.call_i32(99), 25);  // 99 != 0 → else → 5 + 20
}
