use autosynth_ir::{CodeCtx, Operand, VCode};

pub fn assert_block_eq(block: &CodeCtx, expected: &[(VCode, &[Operand])]) {
    let got_vcode: Vec<&VCode> = block.vcode.iter().collect();
    let exp_vcode: Vec<&VCode> = expected.iter().map(|(v, _)| v).collect();

    assert_eq!(got_vcode.len(), exp_vcode.len(),
        "instruction count mismatch: got {}, expected {}\n  got:      {:?}\n  expected: {:?}",
        got_vcode.len(), exp_vcode.len(), got_vcode, exp_vcode);

    let mut op_idx = 0;
    for (i, (exp_inst, exp_ops)) in expected.iter().enumerate() {
        let got_inst = &block.vcode[i];
        assert_eq!(got_inst, exp_inst,
            "instruction {i} mismatch:\n  got:      {got_inst:?}\n  expected: {exp_inst:?}");

        for (j, exp_op) in exp_ops.iter().enumerate() {
            let got_op = block.operands.get(op_idx).unwrap_or_else(|| {
                panic!("instruction {i} operand {j}: missing (only {} operands total)", block.operands.len())
            });
            assert_eq!(got_op, exp_op,
                "instruction {i} operand {j} mismatch:\n  got:      {got_op:?}\n  expected: {exp_op:?}");
            op_idx += 1;
        }
    }

    assert_eq!(op_idx, block.operands.len(),
        "extra operands: consumed {op_idx} but block has {}", block.operands.len());
}
