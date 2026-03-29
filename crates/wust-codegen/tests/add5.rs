#![feature(abi_custom)]

use autosynth_codegen::pipeline::compile;
use autosynth_ir::{AluOp, BlockId, Operand, VCode};
use autosynth_isa::{PReg, UImm12, Width};
use autosynth_select_aarch64::Aarch64Selector;

mod common;

#[test]
fn add5() {
    let module = common::parse_wat(include_str!("add5.wat"));
    let func = common::compile_func(&module, 0);

    let mut selector = Aarch64Selector::new(func.alloc.clone());
    let result = compile(&func, &mut selector).unwrap();

    assert_eq!(result.block_order.len(), 1);
    common::assert_stream_eq(&result.blocks[&BlockId::Entry], &[
        Operand::PReg(PReg(0)).into(),
        Operand::UImm12(UImm12::try_from(5).unwrap()).into(),
        VCode::Alu { op: AluOp::Add },
        Operand::DstPReg(PReg(0), Width::W32).into(),
        VCode::Return,
    ]);

    let module = common::parse_wat(include_str!("add5.wat"));
    let jit = common::jit_compile(&module, 0);
    assert_eq!(jit.call_i32(10), 15);
    assert_eq!(jit.call_i32(0), 5);
    assert_eq!(jit.call_i32(100), 105);
}
