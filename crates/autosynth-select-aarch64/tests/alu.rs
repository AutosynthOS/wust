use autosynth_codegen::pipeline::compile;
use autosynth_ir::{AluOp, BlockId, CodeCtx, Operand, VCode};
use autosynth_isa::{PReg, UImm12, Width};
use autosynth_regalloc::VRegState;
use autosynth_select_aarch64::Aarch64Selector;
use autosynth_test_utils::assert_stream_eq;

/// Helper: build a single-block function with one Alu instruction.
fn build_alu(op: AluOp, lhs_init: VRegState, rhs_init: VRegState) -> autosynth_codegen::ir::IrFunction {
    use std::collections::BTreeMap;
    use autosynth_isa::{IsaReg, PReg};
    let config = autosynth_regalloc::MachineConfig::new(32, BTreeMap::from([
        (IsaReg::FramePointer, PReg(29)),
        (IsaReg::StackPointer, PReg(31)),
        (IsaReg::ReturnAddress, PReg(30)),
        (IsaReg::PlatformReserved, PReg(18)),
    ]));
    let mut f = autosynth_codegen::builder::FunctionBuilder::new(config);

    let lhs = f.define(lhs_init);
    let rhs = f.define(rhs_init);
    let dst = f.define(VRegState { inst_dst: true, ..VRegState::new(Width::W32) });

    f.push_operand(lhs);
    f.push_operand(rhs);
    f.emit(VCode::Alu { op });
    f.emit(VCode::Operand(Operand::DstVReg(dst)));
    f.emit(VCode::Return);

    f.build()
}

/// Helper: build a single-block function with two Alu instructions
/// that both use the same lhs VReg.
fn build_alu_reuse_lhs(
    op: AluOp,
    lhs_init: VRegState,
    rhs1_init: VRegState,
    rhs2_init: VRegState,
) -> autosynth_codegen::ir::IrFunction {
    use std::collections::BTreeMap;
    use autosynth_isa::{IsaReg, PReg};
    let config = autosynth_regalloc::MachineConfig::new(32, BTreeMap::from([
        (IsaReg::FramePointer, PReg(29)),
        (IsaReg::StackPointer, PReg(31)),
        (IsaReg::ReturnAddress, PReg(30)),
        (IsaReg::PlatformReserved, PReg(18)),
    ]));
    let mut f = autosynth_codegen::builder::FunctionBuilder::new(config);

    let lhs = f.define(lhs_init);
    let rhs1 = f.define(rhs1_init);
    let rhs2 = f.define(rhs2_init);
    let dst1 = f.define(VRegState { inst_dst: true, ..VRegState::new(Width::W32) });
    let dst2 = f.define(VRegState { inst_dst: true, ..VRegState::new(Width::W32) });

    f.push_operand(lhs);
    f.push_operand(rhs1);
    f.emit(VCode::Alu { op });
    f.emit(VCode::Operand(Operand::DstVReg(dst1)));

    f.push_operand(lhs);
    f.push_operand(rhs2);
    f.emit(VCode::Alu { op });
    f.emit(VCode::Operand(Operand::DstVReg(dst2)));

    f.emit(VCode::Return);

    f.build()
}

fn compile_entry(func: &autosynth_codegen::ir::IrFunction) -> CodeCtx {
    let mut selector = Aarch64Selector::new(func.alloc.clone());
    let result = compile(func, &mut selector).unwrap();
    result.blocks[&BlockId::Entry(1)].clone()
}

// --- Const folding ---

/// add(param, const(5)): const on rhs folds to UImm12.
///
/// The lhs (x0) is consumed by the add and not used again, so the
/// dst reuses x0 — no register wasted.
#[test]
fn add_const_rhs_folds() {
    let func = build_alu(AluOp::Add, VRegState { preg: Some(PReg(0)), ..VRegState::new(Width::W32) }, VRegState { r#const: Some(5), ..VRegState::new(Width::W32) });
    let block = compile_entry(&func);

    assert_stream_eq(&block, &[
        Operand::PReg(PReg(0)).into(),                        // lhs = param
        Operand::UImm12(UImm12::try_from(5).unwrap()).into(), // rhs folded
        VCode::Alu { op: AluOp::Add },
        Operand::DstPReg(PReg(0), Width::W32).into(),                              // dst reuses x0 (lhs dead)
        VCode::Return,
    ]);
}

/// add(param, const(5000)): 5000 doesn't fit UImm12, must materialize.
///
/// The rhs can't fold, so it gets materialized into x1. The lhs (x0)
/// is not used again, so dst reuses x0.
#[test]
fn add_large_const_rhs_materializes() {
    let func = build_alu(AluOp::Add, VRegState { preg: Some(PReg(0)), ..VRegState::new(Width::W32) }, VRegState { r#const: Some(5000), ..VRegState::new(Width::W32) });
    let block = compile_entry(&func);

    assert_stream_eq(&block, &[
        Operand::PReg(PReg(0)).into(),    // lhs = param
        Operand::Const(5000).into(),      // rhs const, can't fold
        VCode::Materialize,               // materialize 5000 → x1
        Operand::PReg(PReg(1)).into(),    // rhs = materialized
        VCode::Alu { op: AluOp::Add },
        Operand::DstPReg(PReg(0), Width::W32).into(),          // dst reuses x0
        VCode::Return,
    ]);
}

// --- Commutative swap ---

/// add(const(5), param): const on lhs, commutative op.
///
/// ARM64 `add Rd, Rn, #imm` only supports immediate on the rhs.
/// Since add is commutative, the selector swaps lhs/rhs so the
/// const lands on the rhs and folds to UImm12. Semantically
/// identical: a + b == b + a.
#[test]
fn add_const_lhs_swaps() {
    let func = build_alu(AluOp::Add, VRegState { r#const: Some(5), ..VRegState::new(Width::W32) }, VRegState { preg: Some(PReg(0)), ..VRegState::new(Width::W32) });
    let block = compile_entry(&func);

    // After swap: lhs=param(x0), rhs=#5, dst reuses x0.
    assert_stream_eq(&block, &[
        Operand::PReg(PReg(0)).into(),
        Operand::UImm12(UImm12::try_from(5).unwrap()).into(),
        VCode::Alu { op: AluOp::Add },
        Operand::DstPReg(PReg(0), Width::W32).into(),
        VCode::Return,
    ]);
}

// --- Non-commutative const lhs ---

/// sub(const(5), param): const on lhs, non-commutative op.
///
/// sub is not commutative (5 - x != x - 5), so we can't swap.
/// The const must be materialized into a register for the lhs.
/// x0 holds the param, so the const materializes into x1.
#[test]
fn sub_const_lhs_materializes() {
    let func = build_alu(AluOp::Sub, VRegState { r#const: Some(5), ..VRegState::new(Width::W32) }, VRegState { preg: Some(PReg(0)), ..VRegState::new(Width::W32) });
    let block = compile_entry(&func);

    // Both lhs (x1) and rhs (x0) are dead after the sub.
    // Allocator picks first available — x0.
    assert_stream_eq(&block, &[
        Operand::Const(5).into(),         // const needs materialization
        VCode::Materialize,               // materialize 5 → x1
        Operand::PReg(PReg(1)).into(),    // lhs = materialized const
        Operand::PReg(PReg(0)).into(),    // rhs = param
        VCode::Alu { op: AluOp::Sub },
        Operand::DstPReg(PReg(0), Width::W32).into(),          // dst reuses x0 (first freed)
        VCode::Return,
    ]);
}

// --- Liveness: lhs used again ---

/// add(param, const(3)) then add(param, const(7)):
/// lhs (param in x0) is used in both instructions.
///
/// Because lhs is used again after the first add, the first dst
/// CANNOT reuse x0 — that would clobber param before the second
/// use. dst1 must go into a fresh register (x1).
///
/// The second add's dst CAN reuse x0 since param is dead after it.
#[test]
fn add_lhs_reused_needs_fresh_dst() {
    let func = build_alu_reuse_lhs(
        AluOp::Add,
        VRegState { preg: Some(PReg(0)), ..VRegState::new(Width::W32) },
        VRegState { r#const: Some(3), ..VRegState::new(Width::W32) },
        VRegState { r#const: Some(7), ..VRegState::new(Width::W32) },
    );
    let block = compile_entry(&func);

    assert_stream_eq(&block, &[
        // First: dst1 = param + 3 → x1 (can't reuse x0, param still live)
        Operand::PReg(PReg(0)).into(),
        Operand::UImm12(UImm12::try_from(3).unwrap()).into(),
        VCode::Alu { op: AluOp::Add },
        Operand::DstPReg(PReg(1), Width::W32).into(),
        // Second: dst2 = param + 7 → x0 (param dead after this, reuse)
        Operand::PReg(PReg(0)).into(),
        Operand::UImm12(UImm12::try_from(7).unwrap()).into(),
        VCode::Alu { op: AluOp::Add },
        Operand::DstPReg(PReg(0), Width::W32).into(),
        VCode::Return,
    ]);
}
