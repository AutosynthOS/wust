#![feature(abi_custom)]

use autosynth_codegen::pipeline::compile;
use autosynth_ir::{BlockId, Operand, VCode};
use autosynth_select_aarch64::Aarch64Selector;

mod common;

/// add_big(a) = a + 5000
/// 5000 > 4095 — must be materialized, can't fold to UImm12.
#[test]
fn add_big() {
    let module = common::parse_wat(include_str!("add_big.wat"));
    let func = common::compile_func(&module, 0);

    let mut selector = Aarch64Selector::new();
    let result = compile(func, &mut selector).unwrap();

    let block = &result.blocks[&BlockId::Entry];

    // No operand should remain as VReg after selection.
    for op in &block.operands {
        assert!(!matches!(op, Operand::VReg(_)), "unresolved VReg: {op:?}");
    }

    // Execute.
    let module = common::parse_wat(include_str!("add_big.wat"));
    let jit = common::jit_compile(&module, 0);
    assert_eq!(jit.call_i32(10), 5010);
    assert_eq!(jit.call_i32(0), 5000);
}
