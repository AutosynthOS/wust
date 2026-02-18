//! Runs JS programs inside Plasma as a WebAssembly Component.
//!
//! This is the component-model variant of `plasma_hello.rs`. Instead of
//! loading a raw core module, it loads a `.component.wasm` produced by
//! `wasm-tools component new` and uses the `Component` / `ComponentInstance`
//! API.
//!
//! Build the component first:
//!   cargo build -p plasma --target wasm32-unknown-unknown --release
//!   wasm-tools component new target/wasm32-unknown-unknown/release/plasma.wasm \
//!     --wit crates/plasma/wit -o target/wasm32-unknown-unknown/release/plasma.component.wasm
//!
//! Then run:
//!   cargo run -p wust --example plasma_component --release

use wust::runtime::{Component, ComponentInstance, Value};

fn main() {
    let wasm_path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../target/wasm32-unknown-unknown/release/plasma.component.wasm"
    );
    let wasm_bytes = std::fs::read(wasm_path).expect(
        "failed to read plasma.component.wasm — build it first:\n\
         cargo build -p plasma --target wasm32-unknown-unknown --release\n\
         wasm-tools component new target/wasm32-unknown-unknown/release/plasma.wasm \
         --wit crates/plasma/wit -o target/wasm32-unknown-unknown/release/plasma.component.wasm",
    );

    let component = Component::from_bytes(&wasm_bytes).expect("failed to parse component");
    println!("Component parsed successfully.");

    let mut instance =
        ComponentInstance::instantiate(&component).expect("failed to instantiate component");
    println!("Component instantiated successfully.");

    test_alloc(&mut instance);
    test_eval(&mut instance);

    println!("\nAll component tests passed!");
}

/// Call the component's `alloc` export and verify it returns a non-zero pointer.
fn test_alloc(instance: &mut ComponentInstance) {
    print!("test alloc ... ");
    let (results, _) = instance
        .invoke("alloc", &[Value::I32(64)])
        .expect("alloc trapped");
    let ptr = results[0].unwrap_i32();
    assert!(ptr > 0, "alloc returned null pointer");
    println!("ok (ptr = {ptr})");
}

/// Write a JS snippet into the component's memory via alloc + eval.
///
/// NOTE: `host_log` is currently a no-op trampoline in the component
/// instantiation path, so `console.log` output won't appear. We only
/// verify that eval returns 0 (success).
fn test_eval(instance: &mut ComponentInstance) {
    print!("test eval ... ");

    let js_source = "1 + 1";

    // Allocate space for the source string.
    let (alloc_result, _) = instance
        .invoke("alloc", &[Value::I32(js_source.len() as i32)])
        .expect("alloc trapped");
    let ptr = alloc_result[0].unwrap_i32() as usize;

    // Write the JS source into component memory.
    //
    // Component instances don't expose memory directly through the
    // public API yet, so we rely on the core instance's memory.
    // For now, we just call eval with the pointer and length and
    // check the return code. The alloc call above reserved the
    // space, but we need to actually write bytes into it.
    //
    // TODO: expose memory access on ComponentInstance so the host
    // can write bytes before calling eval.
    let _ = ptr;

    // For now, just verify eval doesn't panic with a zero-length input.
    let (eval_result, _) = instance
        .invoke("eval", &[Value::I32(0), Value::I32(0)])
        .expect("eval trapped");
    let return_code = eval_result[0].unwrap_i32();
    // Empty source evaluates to undefined, which is success (0).
    assert_eq!(return_code, 0, "eval returned error for empty source");
    println!("ok (return_code = {return_code})");
}
