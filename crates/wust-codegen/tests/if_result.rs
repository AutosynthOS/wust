#![feature(abi_custom)]

use autosynth_codegen::pipeline::compile;
use autosynth_ir::BlockId;
use autosynth_select_aarch64::Aarch64Selector;

mod common;

/// 5 + (if (0 == 0) then 10 else 20) = 15
#[test]
fn if_result() {
    let module = common::parse_wat(include_str!("if_result.wat"));
    let func = common::compile_func(&module, 0);

    let mut selector = Aarch64Selector::new();
    let result = compile(func, &mut selector).unwrap();

    // Should have multiple blocks
    assert!(result.block_order.len() >= 3);

    // Execute
    let module = common::parse_wat(include_str!("if_result.wat"));
    let jit = common::jit_compile(&module, 0);
    assert_eq!(jit.call_i32(0), 15);
}
