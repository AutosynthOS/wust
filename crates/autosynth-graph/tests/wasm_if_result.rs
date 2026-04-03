//! Test: compile if_result.wat to graph, verify phi nodes, run pipeline.
//!
//! The if_result.wat function:
//!   if (param == 0) then 10 else 20, add 5
//! This tests the if/else/end merge path with divergent operand stack values.

use autosynth_graph::builder;
use autosynth_graph::display::print_timeline;
use autosynth_graph::pathfinder;
use autosynth_graph::timeline::{detect_blocks, topo_sort_and_link};
use autosynth_graph::transforms;
use autosynth_graph::types::*;
use wust_core::ParsedModule;

fn load_module(wat_bytes: &[u8]) -> ParsedModule {
    let wasm = wat::parse_bytes(wat_bytes).expect("failed to parse wat");
    ParsedModule::new(&wasm).expect("failed to parse module")
}

#[test]
fn wasm_if_result_compiles_to_graph() {
    let module = load_module(include_bytes!("if_result.wat"));
    let func = &module.funcs[0];

    let graph = builder::compile(func, &module.funcs);
    let mut ops = graph.ops;
    let mut vregs = graph.vregs;
    let roots = graph.roots;

    // Step 1: topo sort
    let mut sorted = topo_sort_and_link(&roots, &mut ops, &vregs);
    let blocks = detect_blocks(&sorted, &roots, &ops, &vregs);
    print_timeline("if_result (raw)", &blocks, &ops, &vregs);

    // Single return path (implicit return at function end).
    assert_eq!(roots.len(), 1, "expected 1 return root");

    // With a single root, all ops end up in Entry.
    // Verify we have the key operations: param, const 5, eqz, brif,
    // const 10, const 20, phi (add used as placeholder), add, return.

    // Verify phi node exists — the if/else produces two different
    // constants (10 and 20) that merge at End. Our merge uses an ALU
    // Add as a placeholder phi.
    let phi_count = sorted
        .iter()
        .filter(|&&k| {
            let op = &ops[k];
            // A phi is an ALU Add whose both inputs are constants and
            // which was created by the merge (not the final i32.add).
            if !matches!(op.opcode, OpCode::Alu(_)) {
                return false;
            }
            let both_const = op.inputs.iter().all(|input| {
                if let Input::VReg(vreg_key) = input {
                    vregs
                        .get(*vreg_key)
                        .is_some_and(|d| d.constant.is_some())
                } else {
                    false
                }
            });
            both_const && op.inputs.len() == 2
        })
        .count();
    assert!(
        phi_count >= 1,
        "expected at least 1 phi-like merge node, got {phi_count}"
    );

    // Step 2: fold + sweep
    transforms::fold_immediates(&sorted, &mut ops, &vregs);
    let live = transforms::mark_reachable(&roots, &ops, &vregs);
    sorted = transforms::sweep(&sorted, &live, &mut ops, &mut vregs);
    for i in 0..sorted.len() {
        let prev = if i > 0 { Some(sorted[i - 1]) } else { None };
        ops[sorted[i]].prev = prev;
    }

    let blocks = detect_blocks(&sorted, &roots, &ops, &vregs);
    print_timeline("if_result (after fold+sweep)", &blocks, &ops, &vregs);

    // Step 3: pathfinder loop
    let mut pass = 0;
    loop {
        pass += 1;
        let changes = pathfinder::apply_paths(&sorted, &mut ops, &mut vregs);
        println!("Pathfinder pass {pass}: {changes} change(s)");
        if changes == 0 || pass > 10 {
            break;
        }
        sorted = pathfinder::collect_nodes(&roots, &ops);
    }

    // Step 4: final sweep
    let live2 = transforms::mark_reachable(&roots, &ops, &vregs);
    sorted = transforms::sweep(&sorted, &live2, &mut ops, &mut vregs);
    for i in 0..sorted.len() {
        let prev = if i > 0 { Some(sorted[i - 1]) } else { None };
        ops[sorted[i]].prev = prev;
    }

    let blocks = detect_blocks(&sorted, &roots, &ops, &vregs);
    print_timeline("if_result (final)", &blocks, &ops, &vregs);

    // Single root means single block (Entry) — no case splitting.
    assert_eq!(blocks.len(), 1, "expected 1 block (single return root)");
}
