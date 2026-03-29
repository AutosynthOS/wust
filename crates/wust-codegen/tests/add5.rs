#![feature(abi_custom)]

use autosynth_codegen::pipeline::compile;
use autosynth_ir::{AluOp, BlockId, Operand, VCode, VReg};
use autosynth_isa::UImm12;
use autosynth_select_aarch64::Aarch64Selector;

mod common;

#[test]
fn add5() {
    let module = common::parse_wat(include_str!("add5.wat"));
    let func = common::compile_func(&module, 0);

    let mut selector = Aarch64Selector::new(func.alloc.clone());
    let result = compile(&func, &mut selector).unwrap();

    assert_eq!(result.block_order.len(), 1);
    // After selection: VRegs preserved, rhs folded to UImm12.
    // PReg allocation happens in a later pass.
    common::assert_stream_eq(&result.blocks[&BlockId::Entry], &[
        VCode::Alu { op: AluOp::Add },
        Operand::VReg(VReg(0)).into(),
        Operand::UImm12(UImm12::try_from(5).unwrap()).into(),
        Operand::VReg(VReg(2)).into(),
        VCode::Return,
    ]);

    // TODO: execution test needs PReg allocation + convergence passes.
    // let module = common::parse_wat(include_str!("add5.wat"));
    // let jit = common::jit_compile(&module, 0);
    // assert_eq!(jit.call_i32(10), 15);
}
