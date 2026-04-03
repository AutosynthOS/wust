mod common;

use autosynth_graph::{Pool, VCode};
use wust_core::ParsedModule;

#[test]
fn if_result_blocks_from_pool() {
    let wat = include_bytes!("if_result.wat");
    let wasm = wat::parse_bytes(wat).expect("failed to parse WAT");
    let module = ParsedModule::new(&wasm).expect("failed to parse module");
    let func_idx = module.resolve_export("test").expect("export not found");
    let func = &module.funcs[*func_idx as usize];

    let b = common::compile_to_graph(func, &module.funcs);
    let pool = b.pool.borrow();

    let blocks = common::reconstruct_blocks(&pool, &b.roots);

    for block in &blocks {
        println!("--- {:?} ---", block.kind);
        for v in &block.ops {
            println!("  {}", Pool::fmt_node(v));
        }
    }

    // if_result has a single return — phi merge is inside the graph, not multiple roots
    // So we get Entry + one Case block
    assert!(blocks.iter().any(|b| {
        b.ops.iter().any(|v| {
            v.state().op.as_ref().map_or(false, |op| op.code == VCode::Phi)
        })
    }), "should contain a phi node");
}
