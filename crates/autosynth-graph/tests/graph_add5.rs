mod common;

use autosynth_graph::{AluOp, Define, VCode};
use autosynth_isa::PReg;
use wust_core::ParsedModule;

/// add5.wat graph with full SetSlot/ClearSlot chain:
///
/// param_root(w0)
///   → SetSlot(local[0])           ← locals region define
///
/// const_root(5)
///   → SetSlot(operand[0])         ← operand push
///     → ClearSlot                 ← operand pop (for add lhs)
///
/// local.get 0 reads SetSlot(local[0])
///   → SetSlot(operand[4])         ← operand push
///     → ClearSlot                 ← operand pop (for add rhs... wait, local.get pushes param)
///
/// Actually:
///   i32.const 5  → push const(5) to operands
///   local.get 0  → push param's local SetSlot to operands
///   i32.add      → pop both, Add(cleared_param, cleared_const)... wait, stack order
///
/// Wasm stack: push const(5), push param → stack is [const(5), param]
/// i32.add: pop rhs=param, pop lhs=const(5) → Add(const(5), param)
///
/// Wait no. Let me re-read the WAT:
///   (i32.add (local.get $a) (i32.const 5))
/// Which in flat form is:
///   local.get 0   → push param
///   i32.const 5   → push const(5)
///   i32.add       → pop rhs=const(5), pop lhs=param → Add(param, const(5))
///
/// Hmm, but the WAT says `(i32.add (local.get $a) (i32.const 5))` which is
/// `local.get $a; i32.const 5; i32.add`.
///
/// So the chain is:
///   param_root(w0, dirty) → SetSlot(local[0])
///   local.get 0: read SetSlot(local[0]) → SetSlot(operand[op_base+0])
///   const_root(5) → SetSlot(operand[op_base+4])
///   i32.add: pop const → ClearSlot, pop param → ClearSlot
///            Add(cleared_param, cleared_const)
#[test]
fn add5_from_wat() {
    let wat = include_bytes!("add5.wat");
    let wasm = wat::parse_bytes(wat).expect("failed to parse WAT");
    let module = ParsedModule::new(&wasm).expect("failed to parse module");
    let func_idx = module.resolve_export("add5").expect("export not found");
    let func = &module.funcs[*func_idx as usize];

    let b = common::compile_to_graph(func, &module.funcs);
    let _pool = b.pool.borrow();

    let results = b.results();
    assert_eq!(results.len(), 1);
    let result = &results[0];

    // Result is a ClearSlot (it was on the operand stack, then the function ended)
    // Actually no — results() returns what's on the operand stack,
    // and the operand entries ARE SetSlot refs. The Add result was pushed
    // to operands (SetSlot), but we read results() directly from entries.
    // Hmm, let me just check what we get and trace the chain.

    let result_state = result.state();
    // The result is a SetSlot (pushed to operand stack after the add)
    assert_eq!(result_state.op.as_ref().unwrap().code, VCode::SetSlot);

    // Its source is the Add
    let add_ref = &result_state.op.as_ref().unwrap().uses[0].as_vreg().unwrap();
    let add_state = add_ref.state();
    let add_op = add_state.op.as_ref().expect("add should have an op");
    assert_eq!(add_op.code, VCode::Alu(AluOp::Add));
    assert_eq!(add_op.uses.len(), 2);

    // Add's LHS is a ClearSlot (popped from operands)
    let lhs_cleared = add_op.uses[0].as_vreg().unwrap().state();
    assert_eq!(lhs_cleared.op.as_ref().unwrap().code, VCode::ClearSlot);
    // Trace back: ClearSlot → SetSlot(operand) → SetSlot(local) → param_root
    let lhs_op_slot = lhs_cleared.op.as_ref().unwrap().uses[0].as_vreg().unwrap().state();
    assert_eq!(lhs_op_slot.op.as_ref().unwrap().code, VCode::SetSlot);
    let lhs_local_slot = lhs_op_slot.op.as_ref().unwrap().uses[0].as_vreg().unwrap().state();
    assert_eq!(lhs_local_slot.op.as_ref().unwrap().code, VCode::SetSlot);
    let param_root = lhs_local_slot.op.as_ref().unwrap().uses[0].as_vreg().unwrap().state();
    assert_eq!(param_root.preg, Some(PReg(0)));
    assert_eq!(param_root.define, Define::Root);
    assert!(param_root.op.is_none());

    // Add's RHS is a ClearSlot (popped const from operands)
    let rhs_cleared = add_op.uses[1].as_vreg().unwrap().state();
    assert_eq!(rhs_cleared.op.as_ref().unwrap().code, VCode::ClearSlot);
    // Trace back: ClearSlot → SetSlot(operand) → const_root
    let rhs_op_slot = rhs_cleared.op.as_ref().unwrap().uses[0].as_vreg().unwrap().state();
    assert_eq!(rhs_op_slot.op.as_ref().unwrap().code, VCode::SetSlot);
    let const_root = rhs_op_slot.op.as_ref().unwrap().uses[0].as_vreg().unwrap().state();
    assert_eq!(const_root.r#const, Some(5));
    assert_eq!(const_root.define, Define::Root);
    assert!(const_root.op.is_none());
}
