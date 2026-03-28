use autosynth_ir::{CodeCtx, Operand, VCode};

pub fn assert_block_eq(block: &CodeCtx, expected: &[(VCode, &[Operand])]) {
    let exp_vcode: Vec<&VCode> = expected.iter().map(|(v, _)| v).collect();
    let exp_ops: Vec<&Operand> = expected.iter().flat_map(|(_, ops)| ops.iter()).collect();

    let got_vcode: Vec<&VCode> = block.vcode.iter().collect();
    let got_ops: Vec<&Operand> = block.operands.iter().collect();

    assert_eq!(got_vcode, exp_vcode, "vcode mismatch");
    assert_eq!(got_ops, exp_ops, "operands mismatch");
}
