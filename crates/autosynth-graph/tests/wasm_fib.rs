//! Test: compile fib.wat to graph, run full pipeline, verify structure.

use autosynth_graph::builder;
use autosynth_graph::display::print_timeline;
use autosynth_graph::pathfinder;
use autosynth_graph::timeline::{detect_blocks, topo_sort_and_link};
use autosynth_graph::transforms;
use autosynth_graph::types::*;
use wust_core::{FuncIdx, ParsedModule};

fn load_module(wat_bytes: &[u8]) -> ParsedModule {
    let wasm = wat::parse_bytes(wat_bytes).expect("failed to parse wat");
    ParsedModule::new(&wasm).expect("failed to parse module")
}

#[test]
fn wasm_fib_compiles_to_graph() {
    let module = load_module(include_bytes!("fib.wat"));

    let graph = builder::compile::compile(FuncIdx::new(0), &module.funcs);
    let mut ops = graph.ops;
    let mut vregs = graph.vregs;
    let roots: Vec<OpKey> = ops
        .iter()
        .filter(|(_, op)| matches!(op.opcode, autosynth_graph::types::VCode::Return { .. }))
        .map(|(k, _)| k)
        .collect();

    // Step 1: topo sort
    let mut sorted = topo_sort_and_link(&roots, &mut ops, &vregs);
    let blocks = detect_blocks(&sorted, &roots, &ops, &vregs);
    print_timeline("Wasm Fib (raw)", &blocks, &ops, &vregs);

    // Verify we have 2 roots (two return paths: early return + final add).
    assert_eq!(roots.len(), 2, "expected 2 return roots");

    // Verify block structure: Entry, Case(0), Case(1).
    assert_eq!(blocks.len(), 3, "expected 3 blocks");
    assert_eq!(blocks[0].label, "Entry");
    assert_eq!(blocks[1].label, "Case(0)");
    assert_eq!(blocks[2].label, "Case(1)");

    // Entry should have: param, const(0), const(0), const(1), cmp_les, brif
    // (param + 2 declared locals + const for comparison + cmp + brif)
    // Actually depends on what gets swept — let's just verify the shape after pipeline.

    // Step 2: fold + sweep
    transforms::fold_immediates(&sorted, &mut ops, &vregs);
    let live = transforms::mark_reachable(&roots, &ops, &vregs);
    sorted = transforms::sweep(&sorted, &live, &mut ops, &mut vregs);
    for i in 0..sorted.len() {
        let prev = if i > 0 { Some(sorted[i - 1]) } else { None };
        ops[sorted[i]].prev = prev;
    }

    let blocks = detect_blocks(&sorted, &roots, &ops, &vregs);
    print_timeline("Wasm Fib (after fold+sweep)", &blocks, &ops, &vregs);

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
    print_timeline("Wasm Fib (final)", &blocks, &ops, &vregs);

    // Verify final structure
    assert_eq!(blocks.len(), 3, "expected 3 blocks after pipeline");
    assert_eq!(blocks[0].label, "Entry");
    assert_eq!(blocks[1].label, "Case(0)");
    assert_eq!(blocks[2].label, "Case(1)");

    // Entry should have: param, cmp, brif
    assert_eq!(blocks[0].ops.len(), 3, "Entry should have 3 ops");
    assert_eq!(ops[blocks[0].ops[0]].opcode, VCode::Define);
    assert!(
        matches!(ops[blocks[0].ops[1]].opcode, VCode::Alu(_)),
        "second entry op should be ALU (cmp)"
    );
    assert_eq!(ops[blocks[0].ops[2]].opcode, VCode::BrIf);

    // Case(0): return
    assert_eq!(blocks[1].ops.len(), 1, "Case(0) should have 1 op");
    assert_eq!(
        ops[blocks[1].ops[0]].opcode,
        VCode::Return { abi: Abi::WasmJit }
    );
}
