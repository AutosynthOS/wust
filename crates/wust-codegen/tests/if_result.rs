#![feature(abi_custom)]

use autosynth_codegen::pipeline::compile;
use autosynth_ir::{AluOp, BlockId, CompOp, Operand, VCode};
use autosynth_isa::{PReg, UImm12};
use autosynth_select_aarch64::Aarch64Selector;

mod common;

/// 5 + (if (0 == 0) then 10 else 20) = 15
#[test]
fn if_result() {
    let module = common::parse_wat(include_str!("if_result.wat"));
    let func = common::compile_func(&module, 0);

    let mut selector = Aarch64Selector::new(func.alloc.clone());
    let result = compile(&func, &mut selector).unwrap();

    // 4 blocks: Entry, then(User(4)), else(User(6)), merge(User(7))
    assert_eq!(result.block_order.len(), 4);

    // Entry: eqz fused into BrIf. v1=Const(0) → x0, rhs folded to #0.
    common::assert_stream_eq(&result.blocks[&BlockId::Entry], &[
        VCode::BrIf {
            op: CompOp::Eq,
            block_if: BlockId::User(4),
            block_else: BlockId::User(6),
        },
        Operand::PReg(PReg(0)).into(),
        Operand::UImm12(UImm12::try_from(0).unwrap()).into(),
    ]);

    // Then: convergence materializes Const(10) for the phi → x1, branch.
    common::assert_stream_eq(&result.blocks[&BlockId::User(4)], &[
        VCode::Materialize,
        Operand::Const(10).into(),
        Operand::PReg(PReg(1)).into(),
        VCode::Branch { target: BlockId::User(7) },
    ]);

    // Else: convergence materializes Const(20) for the phi → x1, branch.
    common::assert_stream_eq(&result.blocks[&BlockId::User(6)], &[
        VCode::Materialize,
        Operand::Const(20).into(),
        Operand::PReg(PReg(1)).into(),
        VCode::Branch { target: BlockId::User(7) },
    ]);

    // Merge: add(v0=Const(5) → x2, phi → x1) → x0, return.
    common::assert_stream_eq(&result.blocks[&BlockId::User(7)], &[
        VCode::Alu { op: AluOp::Add },
        Operand::PReg(PReg(2)).into(),
        Operand::PReg(PReg(1)).into(),
        Operand::PReg(PReg(0)).into(),
        VCode::Return,
    ]);

    // Execute.
    let jit = common::jit_compile(&module, 0);
    assert_eq!(jit.call_i32(0), 15);
}
