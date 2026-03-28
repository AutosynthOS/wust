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

    let mut selector = Aarch64Selector::new();
    let result = compile(func, &mut selector).unwrap();

    // 4 blocks: Entry, then(User(4)), else(User(6)), merge(User(7))
    assert_eq!(result.block_order.len(), 4);

    // Entry: compare 0 == 0 and branch.
    // No params → v1=Const(0) gets x0 (first free scratch).
    common::assert_block_eq(&result.blocks[&BlockId::Entry], &[
        (VCode::BrIf { op: CompOp::Eq, block_if: BlockId::User(4), block_else: BlockId::User(6) }, &[
            Operand::PReg(PReg(0)),     // v1=Const(0) materialized
            Operand::UImm12(UImm12::try_from(0).unwrap()),  // v2=Const(0) folded
        ]),
    ]);

    // Then: just branch to merge.
    common::assert_block_eq(&result.blocks[&BlockId::User(4)], &[
        (VCode::Branch { target: BlockId::User(7) }, &[]),
    ]);

    // Else: just branch to merge.
    common::assert_block_eq(&result.blocks[&BlockId::User(6)], &[
        (VCode::Branch { target: BlockId::User(7) }, &[]),
    ]);

    // Merge: add(5, phi) + return.
    // v0=Const(5) got x1 (x0 was taken in Entry by v1).
    // phi got x2 (first free after x0, x1).
    // result targets x0 (return CC register).
    common::assert_block_eq(&result.blocks[&BlockId::User(7)], &[
        (VCode::Alu { op: AluOp::Add }, &[
            Operand::PReg(PReg(1)),     // v0=Const(5)
            Operand::PReg(PReg(2)),     // phi
            Operand::PReg(PReg(0)),     // result targets x0
        ]),
        (VCode::Return, &[]),
    ]);
}
