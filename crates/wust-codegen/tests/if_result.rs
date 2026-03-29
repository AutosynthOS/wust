#![feature(abi_custom)]

use autosynth_codegen::pipeline::compile;
use autosynth_ir::{AluOp, BlockId, CompOp, Operand, VCode, VReg};
use autosynth_isa::UImm12;
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

    // Entry: eqz fused into BrIf. rhs Const(0) folded to UImm12.
    // VRegs preserved — no PReg allocation yet.
    common::assert_stream_eq(&result.blocks[&BlockId::Entry], &[
        VCode::BrIf {
            op: CompOp::Eq,
            block_if: BlockId::User(4),
            block_else: BlockId::User(6),
        },
        Operand::VReg(VReg(1)).into(),    // lhs: v1=Const(0)
        Operand::UImm12(UImm12::try_from(0).unwrap()).into(), // rhs folded
    ]);

    // Then: convergence materializes Const(10) for the phi, then branch.
    // v4 = Const(10) — the phi source from this predecessor.
    common::assert_stream_eq(&result.blocks[&BlockId::User(4)], &[
        VCode::Materialize,
        Operand::Const(10).into(),
        Operand::VReg(VReg(4)).into(),
        VCode::Branch { target: BlockId::User(7) },
    ]);

    // Else: convergence materializes Const(20) for the phi, then branch.
    // v5 = Const(20) — the phi source from this predecessor.
    common::assert_stream_eq(&result.blocks[&BlockId::User(6)], &[
        VCode::Materialize,
        Operand::Const(20).into(),
        Operand::VReg(VReg(5)).into(),
        VCode::Branch { target: BlockId::User(7) },
    ]);

    // Merge: add(v0=5, phi) → v7, return.
    // v0 = Const(5), v6 = Phi(v4, v5), v7 = InstDst (add result).
    common::assert_stream_eq(&result.blocks[&BlockId::User(7)], &[
        VCode::Alu { op: AluOp::Add },
        Operand::VReg(VReg(0)).into(),    // lhs = Const(5)
        Operand::VReg(VReg(6)).into(),    // rhs = phi
        Operand::VReg(VReg(7)).into(),    // dst
        VCode::Return,
    ]);

    // TODO: execution test needs PReg allocation pass.
}
