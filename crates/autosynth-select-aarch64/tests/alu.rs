use autosynth_codegen::builder::FunctionBuilder;
use autosynth_codegen::pipeline::compile;
use autosynth_ir::{AluOp, BlockId, Operand, VCode};
use autosynth_isa::{PReg, UImm12, Width};
use autosynth_regalloc::VInit;
use autosynth_select_aarch64::Aarch64Selector;

/// v2 = v0 + const(5)
/// Expect const(5) → UImm12(5).
#[test]
fn add_const_folds_to_uimm12() {
    let mut f = FunctionBuilder::new();
    f.start_block(BlockId::Entry);

    let v0 = f.regalloc.define(VInit::PReg(PReg(0)), Width::W32);
    let v1 = f.regalloc.define(VInit::Const(5), Width::W32);
    let v2 = f.regalloc.define(VInit::InstDst, Width::W32);

    f.push_operand(Operand::VReg { id: v0, width: Width::W32 });
    f.push_operand(Operand::VReg { id: v1, width: Width::W32 });
    f.push_operand(Operand::VReg { id: v2, width: Width::W32 });
    f.emit(VCode::Alu { op: AluOp::Add });

    let func = f.build();
    let mut selector = Aarch64Selector::new();
    let result = compile(func, |ra, input, output| selector.select(ra, input, output)).unwrap();

    let block = &result.blocks[&BlockId::Entry];
    assert_eq!(block.instructions.len(), 1);
    assert_eq!(block.operands[0], Operand::VReg { id: v0, width: Width::W32 });
    assert_eq!(block.operands[1], Operand::UImm12(UImm12::try_from(5).unwrap()));
    assert_eq!(block.operands[2], Operand::VReg { id: v2, width: Width::W32 });
}

/// v2 = v0 + const(5000)
/// 5000 > 4095, doesn't fit UImm12 — stays as VReg.
#[test]
fn add_large_const_stays_vreg() {
    let mut f = FunctionBuilder::new();
    f.start_block(BlockId::Entry);

    let v0 = f.regalloc.define(VInit::PReg(PReg(0)), Width::W32);
    let v1 = f.regalloc.define(VInit::Const(5000), Width::W32);
    let v2 = f.regalloc.define(VInit::InstDst, Width::W32);

    f.push_operand(Operand::VReg { id: v0, width: Width::W32 });
    f.push_operand(Operand::VReg { id: v1, width: Width::W32 });
    f.push_operand(Operand::VReg { id: v2, width: Width::W32 });
    f.emit(VCode::Alu { op: AluOp::Add });

    let func = f.build();
    let mut selector = Aarch64Selector::new();
    let result = compile(func, |ra, input, output| selector.select(ra, input, output)).unwrap();

    let block = &result.blocks[&BlockId::Entry];
    assert_eq!(block.operands[1], Operand::VReg { id: v1, width: Width::W32 });
}

