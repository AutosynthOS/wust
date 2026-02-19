pub mod polyfills;

use wust::runtime::{
    Component, ComponentArg, ComponentInstance, ComponentValue, HostFunc, Store, Value,
};

/// Load and parse the plasma WASM module from the build output directory.
///
/// Panics if the file does not exist. Callers should build plasma first:
///   cargo build -p plasma --target wasm32-unknown-unknown --release
fn load_plasma_wasm() -> Component {
    let wasm_path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../target/wasm32-unknown-unknown/release/plasma.wasm"
    );
    let wasm_bytes = std::fs::read(wasm_path).expect(
        "failed to read plasma.wasm — did you run: \
         cargo build -p plasma --target wasm32-unknown-unknown --release?",
    );
    let component = Component::from_bytes(&wasm_bytes).unwrap();

    component
}

pub fn eval_js(js: &str) -> Vec<ComponentValue> {
    let component = load_plasma_wasm();
    let mut instance = ComponentInstance::instantiate(&component).unwrap();

    panic!("not implemented");
}
