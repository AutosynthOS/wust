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

use std::time::Duration;

use plasma_hello::eval_js;

const BUNDLE_PATH: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/discord-bot-bundle.js");

/// Load the discord.js bundle and run it through plasma with a timeout.
///
/// We expect this to fail -- the test passes as long as we get a
/// documented error rather than a hang or crash. The error output
/// tells us which Node.js APIs need polyfilling.
#[test]
fn discord_bot_bundle_loads_and_reports_missing_apis() {
    // read the bundle source from the file system
    let bundle_source = std::fs::read_to_string(BUNDLE_PATH).unwrap();

    eprintln!(
        "Bundle size: {} bytes ({} lines)",
        bundle_source.len(),
        bundle_source.lines().count(),
    );

    dbg!(eval_js(&bundle_source));
}
