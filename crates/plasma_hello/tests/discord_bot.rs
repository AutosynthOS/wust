//! Integration test: load a bundled discord.js bot through the plasma runtime.
//!
//! This test exercises plasma's JS evaluation against a real-world bundle
//! (discord.js compiled by Bun). The bot will NOT connect to Discord -- it
//! will fail at some point when it hits a missing Node.js API. The purpose
//! of this test is to document exactly WHAT fails so we know which polyfills
//! to implement next.
//!
//! ## Prerequisites
//!
//! 1. Build plasma to WASM:
//!    ```sh
//!    cargo build -p plasma --target wasm32-unknown-unknown --release
//!    ```
//!
//! 2. Bundle the discord bot with Bun:
//!    ```sh
//!    cd crates/plasma_hello/discord-bot
//!    bun install
//!    bun run build.ts > ../discord-bot-bundle.js
//!    ```
//!
//! 3. Run this test:
//!    ```sh
//!    cargo test -p plasma_hello --test discord_bot -- --nocapture
//!    ```

use std::sync::mpsc;
use std::thread;
use std::time::Duration;

use plasma_hello::{eval_js, load_plasma_module, EvalResult};

const BUNDLE_PATH: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/discord-bot-bundle.js"
);

/// Maximum time to wait for JS evaluation before declaring a timeout.
const EVAL_TIMEOUT: Duration = Duration::from_secs(30);

/// Load the discord.js bundle and run it through plasma with a timeout.
///
/// We expect this to fail -- the test passes as long as we get a
/// documented error rather than a hang or crash. The error output
/// tells us which Node.js APIs need polyfilling.
#[test]
fn discord_bot_bundle_loads_and_reports_missing_apis() {
    let bundle_source = match std::fs::read_to_string(BUNDLE_PATH) {
        Ok(s) => s,
        Err(e) => {
            eprintln!(
                "SKIPPED: could not read discord-bot-bundle.js: {e}\n\
                 Build it first:\n  \
                 cd crates/plasma_hello/discord-bot\n  \
                 bun install\n  \
                 bun run build.ts > ../discord-bot-bundle.js"
            );
            return;
        }
    };

    eprintln!("Bundle size: {} bytes ({} lines)",
        bundle_source.len(),
        bundle_source.lines().count(),
    );

    let bundle_source = patch_bundle_for_eval(&bundle_source);
    let result = eval_with_timeout(&bundle_source, EVAL_TIMEOUT);

    eprintln!("\n=== Plasma eval result ===");
    eprintln!("Return code: {}", result.return_code);
    eprintln!("Console output:\n{}", result.log_output);

    eprintln!("\n=== Missing API analysis ===");
    analyze_missing_apis(&result.log_output, result.return_code);
}

/// Patch the Bun bundle to be evaluable in script mode.
///
/// 1. Replace `import.meta.require` with plasma's built-in `require`.
/// 2. Strip the entry point (top-level await) and replace with a
///    synchronous probe that tries to instantiate the Client class.
fn patch_bundle_for_eval(source: &str) -> String {
    let patched = source.replace(
        "var __require = import.meta.require;",
        "var __require = require;",
    );
    strip_entry_point_and_add_probe(&patched)
}

/// Run JS evaluation in a background thread with a timeout.
///
/// Returns the eval result if it completes within the given duration,
/// or a synthetic timeout result otherwise.
fn eval_with_timeout(js_source: &str, timeout: Duration) -> EvalResult {
    let source = js_source.to_string();
    let (tx, rx) = mpsc::channel();

    thread::spawn(move || {
        let module = load_plasma_module();
        let result = eval_js(&module, &source);
        let _ = tx.send(result);
    });

    match rx.recv_timeout(timeout) {
        Ok(result) => result,
        Err(_) => {
            eprintln!("TIMEOUT: JS evaluation did not complete within {timeout:?}");
            EvalResult {
                return_code: -2,
                log_output: format!("[TIMEOUT after {timeout:?}]"),
            }
        }
    }
}

/// Replace the entry point code (top-level await) with a synchronous probe.
///
/// The bundle's last ~30 lines contain the entry point from index.ts which
/// uses top-level `await`. We strip everything from `// index.ts` onwards
/// and replace it with a synchronous call that tries to load the discord.js
/// module and instantiate the Client class.
fn strip_entry_point_and_add_probe(source: &str) -> String {
    let marker = "// index.ts";
    let cut_point = source.find(marker).unwrap_or(source.len());
    let definitions = &source[..cut_point];

    let probe = r#"
// === plasma test probe ===
try {
    var discord = require_src();
    console.log("PROBE: require_src() succeeded");
    console.log("PROBE: discord.Client exists: " + (typeof discord.Client));
    var client = new discord.Client({
        intents: [1, 512, 32768, 4096, 8192],
        partials: [0, 1, 2]
    });
    console.log("PROBE: Client instantiated successfully");
} catch(e) {
    console.log("PROBE ERROR: " + e);
}
"#;

    format!("{definitions}{probe}")
}

/// Binary search the bundle to find where the freeze starts.
///
/// Tries progressively larger line counts: 100, 500, 1000, 5000, 10000,
/// 20000, then the full bundle (minus entry point). Each attempt gets
/// a 10-second timeout. Reports the last working size and first failing size.
#[test]
fn binary_search_bundle_freeze_point() {
    let bundle_source = match std::fs::read_to_string(BUNDLE_PATH) {
        Ok(s) => s,
        Err(_) => { eprintln!("SKIPPED: no bundle"); return; }
    };

    let patched = bundle_source.replace(
        "var __require = import.meta.require;",
        "var __require = require;",
    );

    let lines: Vec<&str> = patched.lines().collect();
    let marker_line = lines.iter().position(|l| l.contains("// index.ts"));
    let max_lines = marker_line.unwrap_or(lines.len());

    eprintln!("Total bundle lines (before entry point): {max_lines}");

    let sizes = [1000, 2000, 3000, 4000, 5000, 7500, 10000, 15000, 20000];
    let timeout = Duration::from_secs(20);

    for &size in &sizes {
        let take = size.min(max_lines);
        let chunk: String = lines[..take].join("\n");
        let source = format!(
            "{chunk}\nconsole.log('CHUNK OK: {take} lines, ' + {take} + ' lines parsed');"
        );

        eprintln!("\n--- Trying {take} lines ({} bytes) ---", source.len());
        let result = eval_with_timeout(&source, timeout);

        if result.return_code == -2 {
            eprintln!("FREEZE at {take} lines. Last output: {}", result.log_output);
            eprintln!("Bundle freezes somewhere between previous size and {take} lines.");
            return;
        }

        eprintln!("OK (rc={}): {}", result.return_code, result.log_output);
        if take == max_lines { break; }
    }
}

/// Analyze the error output to catalog which Node.js APIs are missing.
///
/// Prints a summary of what polyfills are needed based on common
/// error patterns in the output.
fn analyze_missing_apis(output: &str, return_code: i32) {
    let mut missing = Vec::new();

    let api_patterns = [
        ("process", "process (process.env, process.version, etc.)"),
        ("Buffer", "node:buffer (Buffer global)"),
        ("EventEmitter", "node:events (EventEmitter)"),
        ("setTimeout", "timers (setTimeout/setInterval)"),
        ("setInterval", "timers (setInterval)"),
        ("setImmediate", "timers (setImmediate)"),
        ("clearTimeout", "timers (clearTimeout)"),
        ("WebSocket", "WebSocket API"),
        ("fetch", "fetch API (globalThis.fetch)"),
        ("URL", "URL API (globalThis.URL)"),
        ("TextEncoder", "TextEncoder/TextDecoder"),
        ("TextDecoder", "TextEncoder/TextDecoder"),
        ("crypto", "node:crypto"),
        ("require", "CommonJS require()"),
        ("module", "CommonJS module/exports"),
        ("__dirname", "CommonJS __dirname/__filename"),
        ("node:http", "node:http"),
        ("node:https", "node:https"),
        ("node:net", "node:net"),
        ("node:stream", "node:stream"),
        ("node:util", "node:util"),
        ("node:path", "node:path"),
        ("node:os", "node:os"),
        ("node:zlib", "node:zlib"),
        ("AbortController", "AbortController/AbortSignal"),
        ("ReadableStream", "Web Streams API"),
        ("WritableStream", "Web Streams API"),
        ("Promise", "Promise (should be in boa)"),
        ("async", "async/await support"),
    ];

    for (pattern, description) in &api_patterns {
        if output.contains(pattern) {
            missing.push(*description);
        }
    }

    if missing.is_empty() && return_code != 0 {
        eprintln!("No specific API pattern matched in output.");
        eprintln!("The bundle failed with return code {return_code}.");
        eprintln!("Manual inspection of the error is needed.");
    } else if missing.is_empty() && return_code == 0 {
        eprintln!("The bundle ran without errors (unexpected!).");
    } else {
        eprintln!("Detected references to the following APIs in output:");
        for api in &missing {
            eprintln!("  - {api}");
        }
    }
}
