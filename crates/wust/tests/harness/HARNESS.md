# Test Harness

Reusable test harness for `[[test]] harness = false` binaries. Provides
parallel execution, subprocess isolation, live TUI output, and colored
progress bars.

## Quick Start

Add `mod harness;` to your test binary and call the helpers. See
`tests/spec_tests.rs` for a complete example.

## Commands

### Spec Tests

```bash
# Run all spec tests (parallel overview mode):
cargo test -p wust --test spec_tests

# Run a single test (detailed dot grid):
cargo test -p wust --test spec_tests -- i32

# Force detailed mode for multiple tests:
cargo test -p wust --test spec_tests -- f32 --expand

# Filter with exact match:
cargo test -p wust --test spec_tests -- i32 --exact

# Skip tests matching a pattern:
cargo test -p wust --test spec_tests -- --skip f32

# List discovered tests:
cargo test -p wust --test spec_tests -- --list
```

## CLI Flags

These flags are parsed by `parse_cli_args()` and available to all test
binaries using the harness:

| Flag | Description |
|------|-------------|
| `-- <filter>` | Only run tests whose name contains `<filter>` |
| `-- <filter> --exact` | Only run the test with this exact name |
| `--skip <pattern>` | Skip tests whose name contains `<pattern>` (repeatable) |
| `--list` | List discovered test names without running them |
| `--expand` | Force detailed (dot grid) mode even with multiple tests |

## Display Modes

### Overview mode (default for multiple tests)

Tests run in parallel with a live bordered box:

- Top border + title printed immediately
- Completed test rows stream in as they finish (with progress bar, pass/fail count, elapsed time)
- TTY: a live footer shows currently running tests and overall progress
- Non-TTY: rows print as they complete with no cursor movement
- After completion: failing test names, summary bars, and helper commands

### Detailed mode (single test, or `--expand`)

Tests run sequentially in-process. Each test gets a dot grid showing
per-directive pass/fail, a progress bar, and error details.

## Parallel Execution

`run_tests_parallel()` runs tests in subprocess workers:

- Worker count: `std::thread::available_parallelism()` (capped at test count)
- Each test runs in a child process for crash isolation
- Default timeout: 5 seconds per test (configurable via `timeout` param)
- Timed-out tests are killed and marked `TIMED OUT`
- Crashed tests (segfault, signal) are marked `CRASHED`

## Subprocess Protocol

Child processes communicate results via stdout, one line per directive:

```
PASS|FAIL <index> <label>\t<error>
```

The child entry point must:
1. Accept `--__run <name> <path>` args
2. Run the test file
3. Call `print_subprocess_results()` to emit the protocol
4. Exit 0 (all pass) or 1 (some fail)

## Key Types

| Type | Description |
|------|-------------|
| `DirectiveResult` | Result of a single assertion/directive within a test |
| `TestResult` | Aggregated results for one test file (directives, crashed, timed_out, elapsed) |
| `TestEntry` | A test tracked by the parallel runner (name, path, status) |
| `TestStatus` | `Pending`, `Running { started }`, or `Completed(TestResult)` |
| `CliArgs` | Parsed CLI arguments (filter, exact, skip, list, expand) |

## Key Functions

| Function | Description |
|----------|-------------|
| `parse_cli_args()` | Parse CLI flags from `std::env::args()` |
| `discover_test_files(dir, ext)` | Find all files with extension in a directory |
| `matches_filter(name, filter, exact, skip)` | Check if a test name matches CLI filters |
| `run_tests_parallel(title, test_command, tests, timeout, is_tty)` | Run tests in parallel with live TUI |
| `run_test_subprocess_timed(name, path, timeout)` | Run a single test in a child process with timeout |
| `render_dot_grid(name, results)` | Render detailed dot grid for a single test |
| `render_bar(passed, total, width)` | Render a Fira Code progress bar |
| `print_subprocess_results(results)` | Emit subprocess protocol lines (child side) |
| `parse_subprocess_output(stdout)` | Parse subprocess protocol lines (parent side) |
