use crate::*;

#[test]
fn block_params_from_use_def() {
    let mut f = FunctionBuilder::new();

    let base = Register::Phys(29);
    let operands = f.define_vstack(VStack { base, offset: 0 });

    // Block 0: push two constants — both are defs, no external uses.
    f.entry_block(BlockId::Entry);
    let _a = f.push_i32(operands, Value::Const(1));
    let _b = f.push_i32(operands, Value::Const(2));

    // Block 1: pop both (uses), do an add, push result (def).
    f.switch_to_block(BlockId::User(0));
    let rhs = f.pop_i32(operands);
    let lhs = f.pop_i32(operands);
    let dst = f.push_i32_vreg(operands);
    f.emit(IrInst::Alu {
        op: AluOp::Add,
        dst,
        lhs,
        rhs,
    });

    let mut cb = CodeBuilder::new();
    f.build(&mut cb);

    let func = &cb.functions()[0];

    // Entry block: 2 defs (_a, _b), 0 external uses → params should be empty.
    let entry = &func.blocks[0];
    assert_eq!(entry.id, BlockId::Entry);
    assert!(entry.params.is_empty(), "entry block should have no params");
    assert_eq!(entry.results.len(), 2, "entry block defines 2 VRegs");

    // User(0) block: uses _a and _b (not defined here) → they become params.
    let user0 = &func.blocks[1];
    assert_eq!(user0.id, BlockId::User(0));
    assert_eq!(user0.params.len(), 2, "user0 should have 2 params (a, b from entry)");
    // dst is defined here, so it's in results.
    assert!(user0.results.contains(&dst), "user0 should have dst in results");
}
