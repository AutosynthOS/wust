//! Fib graph tests.
//!
//! - fib_timeline: hand-built post-fold/sweep graph, verify block structure.
//! - fib_pipeline: run fold+sweep+pathfinder+sweep on the hand-built graph.
//! - fib_pathfinder: build raw wasm-like graph without pregs on ALU ops,
//!   run full pipeline, verify pathfinder assigns pregs and inserts loads.

use autosynth_graph::display::print_timeline;
use autosynth_graph::op::{AluOp, CmpOp};
use autosynth_graph::pathfinder;
use autosynth_graph::timeline::{detect_blocks, topo_sort_and_link};
use autosynth_graph::transforms;
use autosynth_graph::types::*;
use autosynth_isa::{PReg, UImm12, Width};
use slotmap::SlotMap;
use smallvec::smallvec;

/// Helper to create a vreg definition with a preg hint.
fn vreg_in_preg(vregs: &mut SlotMap<VRegKey, VInit>, from_op: Some(OpKey), preg: PReg) -> VRegKey {
    vregs.insert(VInit {
        width: Width::W32,
        from_op,
        constant: None,
        preg: Some(preg),
        mem: None,
    })
}

/// Helper to create a vreg with no preg assignment.
fn vreg_unassigned(vregs: &mut SlotMap<VRegKey, VInit>, from_op: Some(OpKey)) -> VRegKey {
    vregs.insert(VInit {
        width: Width::W32,
        from_op,
        constant: None,
        preg: None,
        mem: None,
    })
}

/// Helper to create a constant vreg.
fn vreg_const(vregs: &mut SlotMap<VRegKey, VInit>, from_op: Some(OpKey), value: i64) -> VRegKey {
    vregs.insert(VInit {
        width: Width::W32,
        from_op,
        constant: Some(value),
        preg: None,
        mem: None,
    })
}

fn imm(val: u16) -> Input {
    Input::Imm12(UImm12::try_from(val).unwrap())
}

/// Print timeline helper.
fn show(
    label: &str,
    sorted: &[OpKey],
    roots: &[OpKey],
    ops: &SlotMap<OpKey, Operation>,
    vregs: &SlotMap<VRegKey, VInit>,
) {
    let blocks = detect_blocks(sorted, roots, ops, vregs);
    print_timeline(label, &blocks, ops, vregs);
}

// ───────────────────────────────────────────────────────────────────────────
// Test 1: Hand-built post-fold/sweep fib graph — verify block structure
// ───────────────────────────────────────────────────────────────────────────

#[test]
fn fib_timeline() {
    let (ops, vregs, roots) = build_hand_built_fib();
    let mut ops = ops;

    let sorted = topo_sort_and_link(&roots, &mut ops, &vregs);
    let blocks = detect_blocks(&sorted, &roots, &ops, &vregs);
    print_timeline("Fib Timeline", &blocks, &ops, &vregs);

    let mem_0 = MemSlot {
        base: PReg(29),
        offset: 0,
    };

    assert_eq!(blocks.len(), 3);
    assert_eq!(blocks[0].label, "Entry");
    assert_eq!(blocks[0].ops.len(), 3);
    assert_eq!(ops[blocks[0].ops[0]].opcode, VCode::Param);
    assert_eq!(
        ops[blocks[0].ops[1]].opcode,
        VCode::Alu(AluOp::Cmp(CmpOp::LeS))
    );
    assert_eq!(ops[blocks[0].ops[2]].opcode, VCode::BrIf);

    assert_eq!(blocks[1].label, "Case(0)");
    assert_eq!(blocks[1].ops.len(), 1);
    assert_eq!(ops[blocks[1].ops[0]].opcode, VCode::Return);

    assert_eq!(blocks[2].label, "Case(1)");
    assert_eq!(blocks[2].ops.len(), 10);
    assert_eq!(ops[blocks[2].ops[0]].opcode, VCode::SetSlot(mem_0));
    assert_eq!(ops[blocks[2].ops[2]].opcode, VCode::Call(0));
}

// ───────────────────────────────────────────────────────────────────────────
// Test 2: Pipeline on hand-built graph (already correct — pathfinder is no-op)
// ───────────────────────────────────────────────────────────────────────────

#[test]
fn fib_pipeline() {
    let (ops, vregs, roots) = build_hand_built_fib();
    let mut ops = ops;
    let mut vregs = vregs;

    // Step 1: topo sort
    let mut sorted = topo_sort_and_link(&roots, &mut ops, &vregs);
    show("Initial", &sorted, &roots, &ops, &vregs);

    // Step 2: fold + sweep (nothing to fold since already Imm12)
    transforms::fold_immediates(&sorted, &mut ops, &vregs);
    let live = transforms::mark_reachable(&roots, &ops, &vregs);
    sorted = transforms::sweep(&sorted, &live, &mut ops, &mut vregs);
    // Re-link prev pointers after sweep
    for i in 0..sorted.len() {
        let prev = if i > 0 { Some(sorted[i - 1]) } else { None };
        ops[sorted[i]].prev = prev;
    }
    show("After fold+sweep", &sorted, &roots, &ops, &vregs);

    // Step 3: pathfinder (should be 0 changes since all pregs assigned)
    let mut pass = 0;
    loop {
        pass += 1;
        let changes = pathfinder::apply_paths(&sorted, &mut ops, &mut vregs);
        println!("Pathfinder pass {pass}: {changes} change(s)");
        if changes == 0 {
            break;
        }
        sorted = pathfinder::collect_nodes(&roots, &ops);
        // Re-link already done by collect_nodes
    }

    show("After pathfinder", &sorted, &roots, &ops, &vregs);

    // Step 4: final sweep
    let live2 = transforms::mark_reachable(&roots, &ops, &vregs);
    sorted = transforms::sweep(&sorted, &live2, &mut ops, &mut vregs);
    for i in 0..sorted.len() {
        let prev = if i > 0 { Some(sorted[i - 1]) } else { None };
        ops[sorted[i]].prev = prev;
    }
    show("Final", &sorted, &roots, &ops, &vregs);

    // Verify: structure should be unchanged
    let blocks = detect_blocks(&sorted, &roots, &ops, &vregs);
    assert_eq!(blocks.len(), 3);
    assert_eq!(blocks[0].ops.len(), 3, "Entry should have 3 ops");
    assert_eq!(blocks[1].ops.len(), 1, "Case(0) should have 1 op");
    assert_eq!(blocks[2].ops.len(), 10, "Case(1) should have 10 ops");
}

// ───────────────────────────────────────────────────────────────────────────
// Test 3: Raw wasm-like fib graph — pathfinder assigns pregs, inserts loads
// ───────────────────────────────────────────────────────────────────────────

#[test]
fn fib_pathfinder() {
    let (ops, vregs, roots) = build_raw_fib();
    let mut ops = ops;
    let mut vregs = vregs;

    // Step 1: topo sort
    let mut sorted = topo_sort_and_link(&roots, &mut ops, &vregs);
    show("Raw fib (initial)", &sorted, &roots, &ops, &vregs);

    // Step 2: fold immediates (const #1 and #2 become imm12)
    transforms::fold_immediates(&sorted, &mut ops, &vregs);
    let live = transforms::mark_reachable(&roots, &ops, &vregs);
    sorted = transforms::sweep(&sorted, &live, &mut ops, &mut vregs);
    for i in 0..sorted.len() {
        let prev = if i > 0 { Some(sorted[i - 1]) } else { None };
        ops[sorted[i]].prev = prev;
    }
    show("After fold+sweep", &sorted, &roots, &ops, &vregs);

    // Step 3: pathfinder loop
    let mut pass = 0;
    loop {
        pass += 1;
        let changes = pathfinder::apply_paths(&sorted, &mut ops, &mut vregs);
        println!("Pathfinder pass {pass}: {changes} change(s)");
        if changes == 0 {
            break;
        }
        sorted = pathfinder::collect_nodes(&roots, &ops);
    }
    show("After pathfinder", &sorted, &roots, &ops, &vregs);

    // Step 4: final sweep
    let live2 = transforms::mark_reachable(&roots, &ops, &vregs);
    sorted = transforms::sweep(&sorted, &live2, &mut ops, &mut vregs);
    for i in 0..sorted.len() {
        let prev = if i > 0 { Some(sorted[i - 1]) } else { None };
        ops[sorted[i]].prev = prev;
    }

    let blocks = detect_blocks(&sorted, &roots, &ops, &vregs);
    print_timeline("Final (pathfinder)", &blocks, &ops, &vregs);

    // Verify structure
    assert_eq!(blocks.len(), 3, "expected 3 blocks");
    assert_eq!(blocks[0].label, "Entry");
    assert_eq!(blocks[1].label, "Case(0)");
    assert_eq!(blocks[2].label, "Case(1)");

    // Entry: param, cmp_les, brif
    assert_eq!(blocks[0].ops.len(), 3, "Entry should have 3 ops");

    // Case(0): return
    assert_eq!(blocks[1].ops.len(), 1, "Case(0) should have 1 op");

    // Case(1): should have ~10 ops after pathfinder inserts loads and sweep
    // removes dead operand stack bookkeeping
    let case1_len = blocks[2].ops.len();
    println!("Case(1) has {case1_len} ops");

    // Verify all ALU ops have pregs assigned
    for &op_key in &sorted {
        let op = &ops[op_key];
        if let VCode::Alu(_) = op.opcode {
            assert!(!op.defines.is_empty(), "ALU op should have defines");
            for &vreg_key in &op.defines {
                let def = &vregs[vreg_key];
                assert!(def.preg.is_some(), "ALU vreg should have preg assigned");
            }
        }
    }

    // Verify loads were inserted for values crossing calls
    let load_count = sorted
        .iter()
        .filter(|&&k| matches!(ops[k].opcode, VCode::Load(_)))
        .count();
    assert!(
        load_count >= 2,
        "Expected at least 2 loads (v0 and call1 result after calls), got {load_count}"
    );
}

// ───────────────────────────────────────────────────────────────────────────
// Graph builders
// ───────────────────────────────────────────────────────────────────────────

/// Build the hand-built post-fold/sweep fib graph with all pregs assigned
/// and stores/loads already placed.
fn build_hand_built_fib() -> (
    SlotMap<OpKey, Operation>,
    SlotMap<VRegKey, VInit>,
    Vec<OpKey>,
) {
    let mut ops: SlotMap<OpKey, Operation> = SlotMap::with_key();
    let mut vregs: SlotMap<VRegKey, VInit> = SlotMap::with_key();

    let w0 = PReg(0);
    let w1 = PReg(1);
    let x29 = PReg(29);
    let mem_0 = MemSlot {
        base: x29,
        offset: 0,
    };
    let mem_4 = MemSlot {
        base: x29,
        offset: 4,
    };

    // --- Entry ---
    let op_param = ops.insert_with_key(|_| Operation {
        opcode: VCode::Param,
        inputs: smallvec![],
        effect: None,
        prev: None,
        defines: smallvec![],
    });
    let v0 = vreg_in_preg(&mut vregs, op_param, w0);
    ops[op_param].defines = smallvec![v0];

    let op_cmp = ops.insert_with_key(|_| Operation {
        opcode: VCode::Alu(AluOp::Cmp(CmpOp::LeS)),
        inputs: smallvec![Input::VReg(v0), imm(1)],
        effect: None,
        prev: None,
        defines: smallvec![],
    });
    let v1 = vreg_in_preg(&mut vregs, op_cmp, w1);
    ops[op_cmp].defines = smallvec![v1];

    let op_brif = ops.insert_with_key(|_| Operation {
        opcode: VCode::BrIf,
        inputs: smallvec![Input::VReg(v1)],
        effect: None,
        prev: None,
        defines: smallvec![],
    });

    // --- Case(0) ---
    let op_ret0 = ops.insert_with_key(|_| Operation {
        opcode: VCode::Return,
        inputs: smallvec![Input::VReg(v0)],
        effect: Some(op_brif),
        prev: None,
        defines: smallvec![],
    });

    // --- Case(1) ---
    let op_spill_v0 = ops.insert_with_key(|_| Operation {
        opcode: VCode::SetSlot(mem_0),
        inputs: smallvec![Input::VReg(v0)],
        effect: Some(op_brif),
        prev: None,
        defines: smallvec![],
    });

    let op_sub1 = ops.insert_with_key(|_| Operation {
        opcode: VCode::Alu(AluOp::Sub),
        inputs: smallvec![Input::VReg(v0), imm(1)],
        effect: None,
        prev: None,
        defines: smallvec![],
    });
    let v2 = vreg_in_preg(&mut vregs, op_sub1, w0);
    ops[op_sub1].defines = smallvec![v2];

    let op_call1 = ops.insert_with_key(|_| Operation {
        opcode: VCode::Call(0),
        inputs: smallvec![Input::VReg(v2)],
        effect: Some(op_spill_v0),
        prev: None,
        defines: smallvec![],
    });
    let v3 = vreg_in_preg(&mut vregs, op_call1, w0);
    ops[op_call1].defines = smallvec![v3];

    let op_spill_v3 = ops.insert_with_key(|_| Operation {
        opcode: VCode::SetSlot(mem_4),
        inputs: smallvec![Input::VReg(v3)],
        effect: Some(op_call1),
        prev: None,
        defines: smallvec![],
    });

    let op_load_v0 = ops.insert_with_key(|_| Operation {
        opcode: VCode::Load(mem_0),
        inputs: smallvec![],
        effect: Some(op_spill_v3),
        prev: None,
        defines: smallvec![],
    });
    let v4 = vreg_in_preg(&mut vregs, op_load_v0, w1);
    ops[op_load_v0].defines = smallvec![v4];

    let op_sub2 = ops.insert_with_key(|_| Operation {
        opcode: VCode::Alu(AluOp::Sub),
        inputs: smallvec![Input::VReg(v4), imm(2)],
        effect: None,
        prev: None,
        defines: smallvec![],
    });
    let v5 = vreg_in_preg(&mut vregs, op_sub2, w0);
    ops[op_sub2].defines = smallvec![v5];

    let op_call2 = ops.insert_with_key(|_| Operation {
        opcode: VCode::Call(0),
        inputs: smallvec![Input::VReg(v5)],
        effect: Some(op_load_v0),
        prev: None,
        defines: smallvec![],
    });
    let v6 = vreg_in_preg(&mut vregs, op_call2, w0);
    ops[op_call2].defines = smallvec![v6];

    let op_load_v3 = ops.insert_with_key(|_| Operation {
        opcode: VCode::Load(mem_4),
        inputs: smallvec![],
        effect: Some(op_call2),
        prev: None,
        defines: smallvec![],
    });
    let v7 = vreg_in_preg(&mut vregs, op_load_v3, w1);
    ops[op_load_v3].defines = smallvec![v7];

    let op_add = ops.insert_with_key(|_| Operation {
        opcode: VCode::Alu(AluOp::Add),
        inputs: smallvec![Input::VReg(v7), Input::VReg(v6)],
        effect: None,
        prev: None,
        defines: smallvec![],
    });
    let v8 = vreg_in_preg(&mut vregs, op_add, w0);
    ops[op_add].defines = smallvec![v8];

    let op_ret1 = ops.insert_with_key(|_| Operation {
        opcode: VCode::Return,
        inputs: smallvec![Input::VReg(v8)],
        effect: Some(op_call2),
        prev: None,
        defines: smallvec![],
    });

    let roots = vec![op_ret0, op_ret1];
    (ops, vregs, roots)
}

/// Build the raw wasm-like fib graph.
///
/// This mirrors the TS prototype's initial graph: operand stack
/// set_slot/clear_slot for value passing, const ops for literals,
/// spill stores to [x29+0] and [x29+4], but NO pregs on ALU ops
/// and NO load ops. The pathfinder must assign pregs and insert loads.
fn build_raw_fib() -> (
    SlotMap<OpKey, Operation>,
    SlotMap<VRegKey, VInit>,
    Vec<OpKey>,
) {
    let mut ops: SlotMap<OpKey, Operation> = SlotMap::with_key();
    let mut vregs: SlotMap<VRegKey, VInit> = SlotMap::with_key();

    let w0 = PReg(0);
    let x29 = PReg(29);
    let mem_0 = MemSlot {
        base: x29,
        offset: 0,
    };
    let mem_4 = MemSlot {
        base: x29,
        offset: 4,
    };
    // Operand stack slots (wasm stack bookkeeping, will be swept)
    let stk_24 = MemSlot {
        base: x29,
        offset: 24,
    };
    let stk_28 = MemSlot {
        base: x29,
        offset: 28,
    };

    // --- Constants and params ---

    // param() -> v0:w0 (ABI-fixed)
    let op_param = ops.insert_with_key(|_| Operation {
        opcode: VCode::Param,
        inputs: smallvec![],
        effect: None,
        prev: None,
        defines: smallvec![],
    });
    let v0 = vreg_in_preg(&mut vregs, op_param, w0);
    ops[op_param].defines = smallvec![v0];

    // const() -> c1 = 1
    let op_const1 = ops.insert_with_key(|_| Operation {
        opcode: VCode::Const,
        inputs: smallvec![],
        effect: None,
        prev: None,
        defines: smallvec![],
    });
    let c1 = vreg_const(&mut vregs, op_const1, 1);
    ops[op_const1].defines = smallvec![c1];

    // const() -> c2 = 2
    let op_const2 = ops.insert_with_key(|_| Operation {
        opcode: VCode::Const,
        inputs: smallvec![],
        effect: None,
        prev: None,
        defines: smallvec![],
    });
    let c2 = vreg_const(&mut vregs, op_const2, 2);
    ops[op_const2].defines = smallvec![c2];

    // --- Operand stack: push v0, push c1 for cmp ---

    // set_slot [x29+24](v0)  — push v0
    let op_push_v0 = ops.insert_with_key(|_| Operation {
        opcode: VCode::SetSlot(stk_24),
        inputs: smallvec![Input::VReg(v0)],
        effect: None,
        prev: None,
        defines: smallvec![],
    });
    // clear_slot [x29+24](v0) — pop v0
    let _op_pop_v0 = ops.insert_with_key(|_| Operation {
        opcode: VCode::ClearSlot(stk_24),
        inputs: smallvec![Input::VReg(v0)],
        effect: Some(op_push_v0),
        prev: None,
        defines: smallvec![],
    });

    // set_slot [x29+28](c1) — push c1
    let op_push_c1 = ops.insert_with_key(|_| Operation {
        opcode: VCode::SetSlot(stk_28),
        inputs: smallvec![Input::VReg(c1)],
        effect: None,
        prev: None,
        defines: smallvec![],
    });
    // clear_slot [x29+28](c1) — pop c1
    let _op_pop_c1 = ops.insert_with_key(|_| Operation {
        opcode: VCode::ClearSlot(stk_28),
        inputs: smallvec![Input::VReg(c1)],
        effect: Some(op_push_c1),
        prev: None,
        defines: smallvec![],
    });

    // --- cmp_les(v0, c1) -> v_cmp (NO preg assigned) ---
    let op_cmp = ops.insert_with_key(|_| Operation {
        opcode: VCode::Alu(AluOp::Cmp(CmpOp::LeS)),
        inputs: smallvec![Input::VReg(v0), Input::VReg(c1)],
        effect: None,
        prev: None,
        defines: smallvec![],
    });
    let v_cmp = vreg_unassigned(&mut vregs, op_cmp);
    ops[op_cmp].defines = smallvec![v_cmp];

    // brif(v_cmp)
    let op_brif = ops.insert_with_key(|_| Operation {
        opcode: VCode::BrIf,
        inputs: smallvec![Input::VReg(v_cmp)],
        effect: None,
        prev: None,
        defines: smallvec![],
    });

    // --- Case(0): return(v0) ---
    let op_ret0 = ops.insert_with_key(|_| Operation {
        opcode: VCode::Return,
        inputs: smallvec![Input::VReg(v0)],
        effect: Some(op_brif),
        prev: None,
        defines: smallvec![],
    });

    // --- Case(1): recursive fib ---

    // Spill v0 to [x29+0] before first call
    let op_spill_v0 = ops.insert_with_key(|_| Operation {
        opcode: VCode::SetSlot(mem_0),
        inputs: smallvec![Input::VReg(v0)],
        effect: Some(op_brif),
        prev: None,
        defines: smallvec![],
    });

    // sub(v0, c1) -> v_sub1 (NO preg)
    let op_sub1 = ops.insert_with_key(|_| Operation {
        opcode: VCode::Alu(AluOp::Sub),
        inputs: smallvec![Input::VReg(v0), Input::VReg(c1)],
        effect: None,
        prev: None,
        defines: smallvec![],
    });
    let v_sub1 = vreg_unassigned(&mut vregs, op_sub1);
    ops[op_sub1].defines = smallvec![v_sub1];

    // call $0(v_sub1) -> v_call1:w0 (ABI-fixed result)
    let op_call1 = ops.insert_with_key(|_| Operation {
        opcode: VCode::Call(0),
        inputs: smallvec![Input::VReg(v_sub1)],
        effect: Some(op_spill_v0),
        prev: None,
        defines: smallvec![],
    });
    let v_call1 = vreg_in_preg(&mut vregs, op_call1, w0);
    ops[op_call1].defines = smallvec![v_call1];

    // Spill call1 result to [x29+4]
    let op_spill_call1 = ops.insert_with_key(|_| Operation {
        opcode: VCode::SetSlot(mem_4),
        inputs: smallvec![Input::VReg(v_call1)],
        effect: Some(op_call1),
        prev: None,
        defines: smallvec![],
    });

    // sub(v0, c2) -> v_sub2 (NO preg)
    let op_sub2 = ops.insert_with_key(|_| Operation {
        opcode: VCode::Alu(AluOp::Sub),
        inputs: smallvec![Input::VReg(v0), Input::VReg(c2)],
        effect: None,
        prev: None,
        defines: smallvec![],
    });
    let v_sub2 = vreg_unassigned(&mut vregs, op_sub2);
    ops[op_sub2].defines = smallvec![v_sub2];

    // call $0(v_sub2) -> v_call2:w0 (ABI-fixed result)
    let op_call2 = ops.insert_with_key(|_| Operation {
        opcode: VCode::Call(0),
        inputs: smallvec![Input::VReg(v_sub2)],
        effect: Some(op_spill_call1),
        prev: None,
        defines: smallvec![],
    });
    let v_call2 = vreg_in_preg(&mut vregs, op_call2, w0);
    ops[op_call2].defines = smallvec![v_call2];

    // add(v_call1, v_call2) -> v_add (NO preg)
    let op_add = ops.insert_with_key(|_| Operation {
        opcode: VCode::Alu(AluOp::Add),
        inputs: smallvec![Input::VReg(v_call1), Input::VReg(v_call2)],
        effect: None,
        prev: None,
        defines: smallvec![],
    });
    let v_add = vreg_unassigned(&mut vregs, op_add);
    ops[op_add].defines = smallvec![v_add];

    // return(v_add) [after call2]
    let op_ret1 = ops.insert_with_key(|_| Operation {
        opcode: VCode::Return,
        inputs: smallvec![Input::VReg(v_add)],
        effect: Some(op_call2),
        prev: None,
        defines: smallvec![],
    });

    let roots = vec![op_ret0, op_ret1];
    (ops, vregs, roots)
}
