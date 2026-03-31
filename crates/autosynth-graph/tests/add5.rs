use autosynth_graph::{Pool, OpCode, SlotRef};
use autosynth_isa::{PReg, Width};

/// add5: (param i32) (result i32) = param + 5
///
/// Pool should deduplicate identical states and operations.
#[test]
fn add5_graph() {
    let mut pool = Pool::new();

    // param 0 arrives in x0
    let param = pool.define_param(PReg(0), Width::W32);

    // i32.const 5
    let five = pool.define_const(5, Width::W32);

    // i32.add
    let result = pool.binary(OpCode::Add, param, five);

    // All three are distinct
    assert_ne!(param, five);
    assert_ne!(param, result);
    assert_ne!(five, result);

    // Dedup: same const twice → same VRegRef
    let five_again = pool.define_const(5, Width::W32);
    assert_eq!(five, five_again);

    // Dedup: same operation on same inputs → same VRegRef
    let result_again = pool.binary(OpCode::Add, param, five);
    assert_eq!(result, result_again);

    // Different const → different VRegRef
    let ten = pool.define_const(10, Width::W32);
    assert_ne!(five, ten);

    // Same op, different inputs → different VRegRef
    let result_with_ten = pool.binary(OpCode::Add, param, ten);
    assert_ne!(result, result_with_ten);

    // Check the state
    let result_state = pool.get(result);
    assert_eq!(result_state.width, Width::W32);
    assert!(result_state.op.is_some());
    let op = result_state.op.as_ref().unwrap();
    assert_eq!(op.code, OpCode::Add);
    assert_eq!(op.uses.len(), 2);
    assert_eq!(op.uses[0], param);
    assert_eq!(op.uses[1], five);
}

/// Setting a slot on the same value twice with the same slot → same VRegRef.
/// Setting a slot changes the identity.
#[test]
fn set_slot_changes_identity() {
    let mut pool = Pool::new();

    let param = pool.define_param(PReg(0), Width::W32);
    let slot = SlotRef { base: PReg(29), offset: 0 };

    let with_slot = pool.set_slot(param, slot);
    let with_slot_again = pool.set_slot(param, slot);

    // Same slot on same value → same VRegRef
    assert_eq!(with_slot, with_slot_again);

    // But different from the original (no slot)
    assert_ne!(param, with_slot);

    // Different slot → different VRegRef
    let slot2 = SlotRef { base: PReg(29), offset: 4 };
    let with_slot2 = pool.set_slot(param, slot2);
    assert_ne!(with_slot, with_slot2);
}

/// Assigning a PReg changes the identity.
#[test]
fn assign_preg_changes_identity() {
    let mut pool = Pool::new();

    let five = pool.define_const(5, Width::W32);

    // Const with no register
    assert!(pool.get(five).preg.is_none());

    // Assign to x0
    let in_x0 = pool.assign_preg(five, PReg(0));
    assert_ne!(five, in_x0);
    assert_eq!(pool.get(in_x0).preg, Some(PReg(0)));
    assert_eq!(pool.get(in_x0).r#const, Some(5)); // still knows it's const

    // Same assignment again → same VRegRef
    let in_x0_again = pool.assign_preg(five, PReg(0));
    assert_eq!(in_x0, in_x0_again);

    // Different register → different VRegRef
    let in_x1 = pool.assign_preg(five, PReg(1));
    assert_ne!(in_x0, in_x1);
}

/// CSE: same computation on same inputs = same VRegRef,
/// even if created at different "times."
#[test]
fn cse_free() {
    let mut pool = Pool::new();

    let a = pool.define_param(PReg(0), Width::W32);
    let b = pool.define_const(1, Width::W32);

    // Two independent sub(a, b)
    let sub1 = pool.binary(OpCode::Sub, a, b);
    let sub2 = pool.binary(OpCode::Sub, a, b);
    assert_eq!(sub1, sub2);

    // sub(a, b) != sub(b, a) — not commutative in the graph
    let sub_reversed = pool.binary(OpCode::Sub, b, a);
    assert_ne!(sub1, sub_reversed);
}
