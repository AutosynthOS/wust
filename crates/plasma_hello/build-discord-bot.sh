#!/usr/bin/env bash
# Build the discord bot bundle for plasma integration testing.
#
# Usage:
#   ./crates/plasma_hello/build-discord-bot.sh
#
# Prerequisites:
#   - bun (https://bun.sh)
#   - cargo (with wasm32-unknown-unknown target)
#
# This script:
#   1. Builds plasma to WASM
#   2. Installs discord.js dependencies
#   3. Bundles the TypeScript source into a single JS file
#   4. Outputs discord-bot-bundle.js for the integration test

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

echo "==> Building plasma to WASM..."
cargo build -p plasma --target wasm32-unknown-unknown --release

echo "==> Installing discord.js dependencies..."
cd "$SCRIPT_DIR/discord-bot"
bun install

echo "==> Bundling discord bot..."
bun run build.ts > "$SCRIPT_DIR/discord-bot-bundle.js"

BUNDLE_SIZE=$(wc -c < "$SCRIPT_DIR/discord-bot-bundle.js")
echo "==> Bundle created: $SCRIPT_DIR/discord-bot-bundle.js ($BUNDLE_SIZE bytes)"

echo "==> Done! Run the test with:"
echo "    cargo test -p plasma_hello --test discord_bot -- --nocapture"
