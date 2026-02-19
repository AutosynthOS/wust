//! Sanity test: verify plasma can evaluate simple JS through wust.
//!
//! This test does not require the discord bot bundle -- it just checks
//! that the plasma_hello harness works by running trivial JS.
//!
//! ## Prerequisites
//!
//! Build plasma to WASM:
//! ```sh
//! cargo build -p plasma --target wasm32-unknown-unknown --release
//! ```

use plasma_hello::{eval_js, load_plasma_module};

#[test]
fn eval_simple_expression() {
    let module = load_plasma_module();
    let result = eval_js(&module, r#"console.log("hello from plasma")"#);

    assert_eq!(result.return_code, 0, "eval returned error");
    assert_eq!(result.log_output, "hello from plasma");
}

#[test]
fn eval_arithmetic() {
    let module = load_plasma_module();
    let result = eval_js(&module, "console.log(2 + 2)");

    assert_eq!(result.return_code, 0, "eval returned error");
    assert_eq!(result.log_output, "4");
}

#[test]
fn eval_syntax_error_returns_error_code() {
    let module = load_plasma_module();
    let result = eval_js(&module, "this is not valid javascript {{{");

    assert_ne!(result.return_code, 0, "eval should return error for syntax error");
}

#[test]
fn eval_process_exists() {
    let module = load_plasma_module();
    let result = eval_js(
        &module,
        r#"console.log(typeof process !== "undefined" ? "yes" : "no")"#,
    );

    assert_eq!(result.return_code, 0, "eval failed: {}", result.log_output);
    assert_eq!(result.log_output, "yes");
}

#[test]
fn eval_buffer_exists() {
    let module = load_plasma_module();
    let result = eval_js(
        &module,
        r#"console.log(typeof Buffer !== "undefined" ? "yes" : "no")"#,
    );

    assert_eq!(result.return_code, 0, "eval failed: {}", result.log_output);
    assert_eq!(result.log_output, "yes");
}

#[test]
fn eval_event_emitter_exists() {
    let module = load_plasma_module();
    let result = eval_js(
        &module,
        r#"console.log(typeof EventEmitter !== "undefined" ? "yes" : "no")"#,
    );

    assert_eq!(result.return_code, 0, "eval failed: {}", result.log_output);
    assert_eq!(result.log_output, "yes");
}

#[test]
fn eval_polyfills_timing() {
    use std::time::Instant;
    let module = load_plasma_module();

    let start = Instant::now();
    let result = eval_js(&module, "console.log('done')");
    let elapsed = start.elapsed();

    eprintln!("Polyfills eval time: {elapsed:?}");
    assert_eq!(result.return_code, 0, "eval failed: {}", result.log_output);
    assert!(elapsed.as_secs() < 10, "polyfills took too long: {elapsed:?}");
}

#[test]
fn eval_commonjs_pattern() {
    let module = load_plasma_module();
    let js = r#"
var __commonJS = function(cb, mod) {
    return function() {
        if (!mod) {
            mod = { exports: {} };
            cb(mod.exports, mod);
        }
        return mod.exports;
    };
};
var require_foo = __commonJS(function(exports, module) {
    exports.hello = "world";
});
var foo = require_foo();
console.log(foo.hello);
"#;
    let result = eval_js(&module, js);
    assert_eq!(result.return_code, 0, "eval failed: {}", result.log_output);
    assert_eq!(result.log_output, "world");
}

#[test]
fn require_node_events_returns_event_emitter() {
    let module = load_plasma_module();
    let js = r#"
var events = require("node:events");
var ee = new events();
ee.on("test", function() { console.log("event fired"); });
ee.emit("test");
"#;
    let result = eval_js(&module, js);
    assert_eq!(result.return_code, 0, "eval failed: {}", result.log_output);
    assert_eq!(result.log_output, "event fired");
}

#[test]
fn require_node_events_default_is_event_emitter() {
    let module = load_plasma_module();
    let js = r#"
var EventEmitter = require("node:events");
console.log(typeof EventEmitter === "function" ? "yes" : "no");
"#;
    let result = eval_js(&module, js);
    assert_eq!(result.return_code, 0, "eval failed: {}", result.log_output);
    assert_eq!(result.log_output, "yes");
}

#[test]
fn require_node_buffer_returns_buffer() {
    let module = load_plasma_module();
    let js = r#"
var buf = require("node:buffer");
console.log(typeof buf.Buffer === "function" ? "yes" : "no");
"#;
    let result = eval_js(&module, js);
    assert_eq!(result.return_code, 0, "eval failed: {}", result.log_output);
    assert_eq!(result.log_output, "yes");
}

#[test]
fn require_node_process_returns_process() {
    let module = load_plasma_module();
    let js = r#"
var proc = require("node:process");
console.log(proc.platform);
"#;
    let result = eval_js(&module, js);
    assert_eq!(result.return_code, 0, "eval failed: {}", result.log_output);
    assert_eq!(result.log_output, "wasm");
}

#[test]
fn require_node_timers_returns_timer_functions() {
    let module = load_plasma_module();
    let js = r#"
var timers = require("node:timers");
console.log(typeof timers.setTimeout === "function" ? "yes" : "no");
"#;
    let result = eval_js(&module, js);
    assert_eq!(result.return_code, 0, "eval failed: {}", result.log_output);
    assert_eq!(result.log_output, "yes");
}

#[test]
fn require_node_url_returns_url() {
    let module = load_plasma_module();
    let js = r#"
var url = require("node:url");
var u = new url.URL("https://example.com/path");
console.log(u.hostname);
"#;
    let result = eval_js(&module, js);
    assert_eq!(result.return_code, 0, "eval failed: {}", result.log_output);
    assert_eq!(result.log_output, "example.com");
}

#[test]
fn require_node_util_deprecate_returns_original() {
    let module = load_plasma_module();
    let js = r#"
var util = require("node:util");
var fn = util.deprecate(function() { return 42; }, "deprecated");
console.log(typeof fn === "function" ? "yes" : "no");
"#;
    let result = eval_js(&module, js);
    assert_eq!(result.return_code, 0, "eval failed: {}", result.log_output);
    assert_eq!(result.log_output, "yes");
}

#[test]
fn require_node_path_parse() {
    let module = load_plasma_module();
    let js = r#"
var path = require("node:path");
var parsed = path.parse("/foo/bar/baz.txt");
console.log(parsed.base);
"#;
    let result = eval_js(&module, js);
    assert_eq!(result.return_code, 0, "eval failed: {}", result.log_output);
    assert_eq!(result.log_output, "baz.txt");
}

#[test]
fn require_unknown_module_throws() {
    let module = load_plasma_module();
    let js = r#"
try {
    require("nonexistent-module");
    console.log("no error");
} catch(e) {
    console.log("caught: " + e.message);
}
"#;
    let result = eval_js(&module, js);
    assert_eq!(result.return_code, 0, "eval failed: {}", result.log_output);
    assert!(
        result.log_output.contains("nonexistent-module"),
        "error should mention module name: {}",
        result.log_output
    );
}

#[test]
fn require_node_timers_promises_returns_promise_timers() {
    let module = load_plasma_module();
    let js = r#"
var tp = require("node:timers/promises");
console.log(typeof tp.setTimeout === "function" ? "yes" : "no");
"#;
    let result = eval_js(&module, js);
    assert_eq!(result.return_code, 0, "eval failed: {}", result.log_output);
    assert_eq!(result.log_output, "yes");
}
