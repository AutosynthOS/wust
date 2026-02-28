# Test Harness

Reusable test harness for `[[test]] harness = false` binaries. Provides
parallel execution, subprocess isolation, live TUI output, and colored
progress bars.

## Quick Start

Add `mod harness;` to your test binary and call the helpers. See
`tests/spec_tests.rs` for a complete example.

## Commands

### Spec Tests

Every spec test runs twice: once through the interpreter (`int::`) and once
through the JIT compiler (`jit::`). Test names are prefixed accordingly:

```
int::spec_i32    # interpreter mode
jit::spec_i32    # JIT mode
```

```bash
# Run all spec tests (both int + jit, parallel overview mode):
cargo test -p wust --test spec_tests

# Run only interpreter tests:
cargo test -p wust --test spec_tests -- int::

# Run only JIT tests:
cargo test -p wust --test spec_tests -- jit::

# Run a single test (detailed dot grid):
cargo test -p wust --test spec_tests i32

# Run a single test in one mode only:
cargo test -p wust --test spec_tests -- jit::spec_i32 --exact

# Force detailed mode for multiple tests:
cargo test -p wust --test spec_tests f32 -- --expand

# Show all errors (no cap) in detailed mode:
cargo test -p wust --test spec_tests block -- --verbose

# Filter with exact match:
cargo test -p wust --test spec_tests i32 -- --exact

# Skip tests matching a pattern:
cargo test -p wust --test spec_tests -- --skip f32

# List discovered tests:
cargo test -p wust --test spec_tests -- --list
```

> **Note:** Positional filter names (like `i32`) can go before or after `--`.
> Flags like `--skip`, `--list`, `--expand`, `--exact`, `--verbose` must go
> after `--` to prevent cargo from consuming them.

## CLI Flags

These flags are parsed by `parse_cli_args()` and available to all test
binaries using the harness:

| Flag | Description |
|------|-------------|
| `<filter>` | Only run tests whose name contains `<filter>` |
| `-- --exact` | Combined with a filter, only run the test with that exact name |
| `-- --skip <pattern>` | Skip tests whose name contains `<pattern>` (repeatable) |
| `-- --list` | List discovered test names without running them |
| `-- --expand` | Force detailed (dot grid) mode even with multiple tests |
| `-- --verbose` / `-v` | Show all errors (no cap) in detailed mode |

## Display Modes

### Overview mode (default for multiple tests)

Tests run in parallel with a live bordered box:

- Top border + title printed immediately
- Completed test rows stream in as they finish (table-aligned with
  progress bar, pass/fail count, elapsed time)
- TTY: a live footer shows running tests, file/directive progress bars,
  and summary stats (redrawn in-place)
- Non-TTY: rows print as they complete with no cursor movement
- After completion: failing test names and summary bars

### Detailed mode (single test, or `--expand`)

Each completed test renders an inner box with:

- Header row (icon, name, progress bar, stats, elapsed)
- Dot grid showing per-directive pass/fail
- Error diagnostics with source snippets (Rust compiler style):
  - Combined `#N: label - error message` header (wrapped if long)
  - Source lines with line number gutter
  - `^^^` underline on the first source line
- Capped at 6 errors by default; use `--verbose` to show all

## Parallel Execution

`run_tests_parallel()` runs tests in subprocess workers:

- Worker count: `std::thread::available_parallelism()` (capped at test count)
- Each test runs in a child process for crash isolation
- Default timeout: 5 seconds per test (configurable via `timeout` param)
- Timed-out tests are killed and marked `TIMEOUT`
- Crashed tests (segfault, signal) are marked `CRASHED`

## Subprocess Protocol

Child processes communicate results via stdout, one line per directive:

```
PASS|FAIL <index> <label>\t<error>\t<line>\t<source>
```

Fields after label are tab-separated. Source newlines are escaped as
literal `\n` in the protocol. The `line` field is a 1-indexed line number;
`source` is the full s-expression text of the directive.

The child entry point must:
1. Accept `--__run <name> <path>` args
2. Run the test file
3. Call `print_subprocess_results()` to emit the protocol
4. Exit 0 (all pass) or 1 (some fail)

## Key Types

| Type | Description |
|------|-------------|
| `DirectiveResult` | Result of a single directive (index, passed, label, error, line, source) |
| `TestResult` | Aggregated results for one test file (directives, crashed, timed_out, elapsed) |
| `TestEntry` | A test tracked by the parallel runner (name, path, status) |
| `TestStatus` | `Pending`, `Running { started }`, or `Completed(TestResult)` |
| `CliArgs` | Parsed CLI arguments (filter, exact, skip, list, expand, verbose) |

## Key Functions

| Function | Description |
|----------|-------------|
| `parse_cli_args()` | Parse CLI flags from `std::env::args()` |
| `discover_test_files(dir, ext)` | Find all files with extension in a directory |
| `matches_filter(name, filter, exact, skip)` | Check if a test name matches CLI filters |
| `run_tests_parallel(title, tests, timeout, is_tty, detailed, verbose)` | Run tests in parallel with live TUI |
| `run_test_subprocess_timed(name, path, timeout)` | Run a single test in a child process with timeout |
| `render_bar(passed, total, width)` | Render a Fira Code progress bar |
| `render_bar_three(passed, failed, total, width)` | Three-state progress bar (green/red/dim) |
| `print_subprocess_results(results)` | Emit subprocess protocol lines (child side) |
| `parse_subprocess_output(stdout)` | Parse subprocess protocol lines (parent side) |
