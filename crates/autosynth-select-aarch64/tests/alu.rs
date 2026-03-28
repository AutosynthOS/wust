use autosynth_codegen::builder::FunctionBuilder;
use autosynth_codegen::pipeline::compile;
use autosynth_ir::{AluOp, BlockId, Operand, VCode, VReg};
use autosynth_isa::{PReg, UImm12, Width};
use autosynth_regalloc::VInit;
use autosynth_select_aarch64::Aarch64Selector;

/// v2 = v0 + const(5)
/// After both passes: lhs=PReg(x0), rhs=UImm12(5), dst=PReg(x0).
#[test]
fn add_const_folds_to_uimm12() {
    let mut f = FunctionBuilder::new();

    let v0 = f.regalloc.define(VInit::PReg(PReg(0)), Width::W32);
    let v1 = f.regalloc.define(VInit::Const(5), Width::W32);
    let v2 = f.regalloc.define(VInit::InstDst, Width::W32);

    f.push_operand(Operand::VReg(VReg::Def(v0)));
    f.push_operand(Operand::VReg(VReg::Def(v1)));
    f.push_operand(Operand::VReg(VReg::Def(v2)));
    f.emit(VCode::Alu { op: AluOp::Add });

    let func = f.build();
    let mut selector = Aarch64Selector::new();
    let result = compile(func, &mut selector).unwrap();

    let block = &result.blocks[&BlockId::Entry];
    assert_eq!(block.vcode.len(), 1);
    assert_eq!(block.operands[0], Operand::PReg(PReg(0)));
    assert_eq!(block.operands[1], Operand::UImm12(UImm12::try_from(5).unwrap()));
    assert_eq!(block.operands[2], Operand::PReg(PReg(0)));
}

/// v2 = v0 + const(5000)
/// 5000 doesn't fit UImm12 — must be materialized into a PReg.
/// No VReg operands should remain after selection.
#[test]
fn add_large_const_materializes() {
    let mut f = FunctionBuilder::new();

    let v0 = f.regalloc.define(VInit::PReg(PReg(0)), Width::W32);
    let v1 = f.regalloc.define(VInit::Const(5000), Width::W32);
    let v2 = f.regalloc.define(VInit::InstDst, Width::W32);

    f.push_operand(Operand::VReg(VReg::Def(v0)));
    f.push_operand(Operand::VReg(VReg::Def(v1)));
    f.push_operand(Operand::VReg(VReg::Def(v2)));
    f.emit(VCode::Alu { op: AluOp::Add });

    let func = f.build();
    let mut selector = Aarch64Selector::new();
    let result = compile(func, &mut selector).unwrap();

    let block = &result.blocks[&BlockId::Entry];

    // No VReg operands should remain.
    for op in &block.operands {
        assert!(!matches!(op, Operand::VReg(_)), "unresolved VReg: {op:?}");
    }

    // Should have materialization instruction(s) before the Alu.
    assert!(block.vcode.len() > 1, "expected materialization + alu, got {:?}", block.vcode);
}
