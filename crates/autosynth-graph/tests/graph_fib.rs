mod common;

use std::rc::Rc;

use autosynth_graph::select::Pipeline;
use autosynth_graph::selectors::{FoldImm, FuseSlots, PropagateTargets, SpillReload};
use autosynth_graph::{NodeRef, Pool};
use wust_core::ParsedModule;

/// Expected Result
///
///   --- Entry ---
/// v0:w0  = param(x0)
/// v1     = Cmp(LeS)(v0:w0, #1)
/// v2     = BrIf(v1)
///
/// --- Case(0) ---
/// v3:w0  = return(v0:w0) [after v2]
///
/// --- Case(1) ---
/// v4     = Store(v0:w0, [x29+0]) [after v2]
/// v5:w0  = Sub(v0:w0, #1)
/// v6:w0  = call $0(v5:w0) [after v4]
/// v7     = Store(v6:w0, [x29+4]) [after v6]
/// v8:w0  = Load([x29+0]) [after v7]
/// v9:w0  = Sub(v8:w0, #2)
/// v10:w0 = call $0(v9:w0) [after v7]
/// v11:w1 = Load([x29+4]) [after v10]
/// v12:w0 = Add(v10:w0, v11:w1)
/// v13:w0 = return(v12:w0) [after v10]
#[test]
fn fib_with_selector_pipeline() {
    let wat = include_bytes!("fib.wat");
    let wasm = wat::parse_bytes(wat).expect("failed to parse WAT");
    let module = ParsedModule::new(&wasm).expect("failed to parse module");
    let func_idx = module.resolve_export("fib").expect("export not found");
    let func = &module.funcs[*func_idx as usize];

    let b = common::compile_to_graph(func, &module.funcs);
    let mut pool = b.pool.borrow_mut();

    let mut pipeline = Pipeline::new();
    // pipeline.add(Box::new(FoldImm));
    // pipeline.add(Box::new(PropagateTargets::new()));
    // pipeline.add(Box::new(SpillReload::new()));

    for node in pool.cache.values() {
        match node.upgrade() {
            Some(node) => {
                println!("{}", Pool::fmt_node(&NodeRef(node)));
            }
            None => {}
        }
    }

    let roots = pipeline.run(&mut pool, &b.roots);

    let blocks = common::reconstruct_blocks(&pool, &roots);
    for block in &blocks {
        println!("--- {:?} ---", block.kind);
        for v in &block.ops {
            println!("  {}", Pool::fmt_node(v));
        }
    }
}
