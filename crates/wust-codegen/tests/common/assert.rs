use std::collections::VecDeque;
use autosynth_ir::{CodeCtx, Operand, VCode};

pub fn assert_block_eq(block: &CodeCtx, expected: &[(VCode, &[Operand])]) {
    let exp_vcode: Vec<&VCode> = expected.iter().map(|(v, _)| v).collect();
    let exp_ops: Vec<&Operand> = expected.iter().flat_map(|(_, ops)| ops.iter()).collect();

    let got_vcode: Vec<&VCode> = block.vcode.iter().collect();
    let got_ops: Vec<&Operand> = block.operands.iter().collect();

    if got_vcode != exp_vcode || got_ops != exp_ops {
        let mut msg = String::new();

        msg.push_str("\n--- expected ---\n");
        let mut idx = 0;
        for (inst, ops) in expected {
            msg.push_str(&format!("  {inst:?}\n"));
            for op in *ops {
                msg.push_str(&format!("    [{idx}] {op:?}\n"));
                idx += 1;
            }
        }

        msg.push_str("--- got ---\n");
        // We don't know arity, so just list instructions then operands
        for inst in &block.vcode {
            msg.push_str(&format!("  {inst:?}\n"));
        }
        for (i, op) in block.operands.iter().enumerate() {
            msg.push_str(&format!("    [{i}] {op:?}\n"));
        }

        panic!("block mismatch:{msg}");
    }
}
