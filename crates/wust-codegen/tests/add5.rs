#![feature(abi_custom)]

use autosynth_codegen::pipeline::compile;
use autosynth_ir::{AluOp, BlockId, Operand, VCode};
use autosynth_isa::UImm12;
use autosynth_select_aarch64::Aarch64Selector;

mod common;

#[test]
fn add5() {
    let module = common::parse_wat(include_str!("add5.wat"));
    let func = common::compile_func(&module, 0);

    let mut selector = Aarch64Selector::new();
    let result = compile(func, &mut selector).unwrap();

    let block = &result.blocks[&BlockId::Entry];
    assert_eq!(block.vcode.len(), 2);
    assert!(matches!(block.vcode[0], VCode::Alu { op: AluOp::Add }));
    assert!(matches!(block.vcode[1], VCode::Return));
    assert_eq!(block.operands[1], Operand::UImm12(UImm12::try_from(5).unwrap()));

    let module = common::parse_wat(include_str!("add5.wat"));
    let jit = common::jit_compile(&module, 0);
    assert_eq!(jit.call_i32(10), 15);
    assert_eq!(jit.call_i32(0), 5);
    assert_eq!(jit.call_i32(100), 105);
}
