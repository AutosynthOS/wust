use autosynth_codegen::pipeline::compile;
use autosynth_ir::{AluOp, BlockId, Operand, VCode};
use autosynth_isa::{UImm12, Width};
use autosynth_select_aarch64::Aarch64Selector;

mod common;

/// add5(a) = a + 5
///
/// Expected VCode after selection:
///   Block Entry: [Alu { Add }]
///   Operands:    [VReg(v0), UImm12(5), VReg(v1), Return]
#[test]
fn add5_vcode() {
    let module = common::parse_wat(include_str!("add5.wat"));
    let func = common::compile_func(&module, 0);

    let mut selector = Aarch64Selector::new();
    let result = compile(func, &mut selector).unwrap();

    let block = &result.blocks[&BlockId::Entry];

    // Should have: Alu { Add }, Return
    assert_eq!(block.instructions.len(), 2);
    assert!(matches!(block.instructions[0], VCode::Alu { op: AluOp::Add }));
    assert!(matches!(block.instructions[1], VCode::Return));

    // Alu operands: VReg(v0), UImm12(5), VReg(v1)
    assert_eq!(block.operands[1], Operand::UImm12(UImm12::try_from(5).unwrap()));
}
