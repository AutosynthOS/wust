//! Reusable test harness with colored output, progress bars, and subprocess
//! isolation for crash safety.
//!
//! # Usage
//!
//! Any `[[test]] harness = false` binary can use this module by adding
//! `mod harness;` and calling the rendering / CLI helpers.
//!
//! # Common commands
//!
//! Run all spec tests (overview mode):
//!   cargo test -p wust --test spec_tests
//!
//! Run a single spec test (detailed dot grid):
//!   cargo test -p wust --test spec_tests -- i32
//!
//! Force detailed mode for multiple tests:
//!   cargo test -p wust --test spec_tests -- f32 --expand
//!
//! Filter with exact match:
//!   cargo test -p wust --test spec_tests -- i32 --exact
//!
//! Skip tests matching a pattern:
//!   cargo test -p wust --test spec_tests -- --skip f32
//!
//! List discovered tests:
//!   cargo test -p wust --test spec_tests -- --list

use std::collections::VecDeque;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

// --- ANSI color codes ---

pub const BOLD: &str = "\x1b[1m";
pub const DIM: &str = "\x1b[2m";
pub const GREEN: &str = "\x1b[1;32m";
pub const RED: &str = "\x1b[1;31m";
pub const RESET: &str = "\x1b[0m";

// --- Fira Code progress bar glyphs (Unicode PUA U+EE00..EE05) ---

const BAR_LEFT_EMPTY: char = '\u{EE00}';
const BAR_MID_EMPTY: char = '\u{EE01}';
const BAR_RIGHT_EMPTY: char = '\u{EE02}';
const BAR_LEFT_FILLED: char = '\u{EE03}';
const BAR_MID_FILLED: char = '\u{EE04}';
const BAR_RIGHT_FILLED: char = '\u{EE05}';

// --- Types ---

/// Result of running a single directive / assertion within a test file.
pub struct DirectiveResult {
    pub index: usize,
    pub passed: bool,
    pub label: String,
    pub error: Option<String>,
}

/// Aggregated results for one test file.
pub struct TestResult {
    pub name: String,
    pub directives: Vec<DirectiveResult>,
    /// Set when the child process crashed (segfault, etc.)
    pub crashed: bool,
    /// Set when the child process exceeded the timeout.
    pub timed_out: bool,
    /// Wall-clock time the test took to run.
    pub elapsed: Duration,
}

impl TestResult {
    pub fn total(&self) -> usize {
        self.directives.len()
    }

    pub fn passed(&self) -> usize {
        self.directives.iter().filter(|r| r.passed).count()
    }

    pub fn failed(&self) -> usize {
        self.total() - self.passed()
    }

    pub fn is_fail(&self) -> bool {
        self.crashed || self.timed_out || self.failed() > 0
    }
}

// --- CLI ---

/// Parsed command-line arguments for the test harness.
///
/// Supports a subset of `cargo test` flags plus our custom `--expand`.
pub struct CliArgs {
    pub filter: Option<String>,
    pub exact: bool,
    pub skip: Vec<String>,
    pub list: bool,
    pub expand: bool,
}

pub fn parse_cli_args() -> CliArgs {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut filter = None;
    let mut exact = false;
    let mut skip = vec![];
    let mut list = false;
    let mut expand = false;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--exact" => exact = true,
            "--list" => list = true,
            "--expand" => expand = true,
            "--skip" => {
                i += 1;
                if i < args.len() {
                    skip.push(args[i].clone());
                }
            }
            // Ignore unknown flags for cargo test compat.
            s if s.starts_with('-') => {}
            // First positional arg is the filter.
            s => {
                if filter.is_none() {
                    filter = Some(s.to_string());
                }
            }
        }
        i += 1;
    }
    CliArgs { filter, exact, skip, list, expand }
}

/// Check whether a test name matches the filter/skip/exact args.
pub fn matches_filter(name: &str, filter: Option<&str>, exact: bool, skip: &[String]) -> bool {
    if let Some(filter) = filter {
        if exact {
            if name != filter {
                return false;
            }
        } else if !name.contains(filter) {
            return false;
        }
    }
    for s in skip {
        if name.contains(s.as_str()) {
            return false;
        }
    }
    true
}

// --- Discovery ---

/// Discover all files with the given extension in a directory.
/// Returns `(stem, path)` pairs sorted by name.
pub fn discover_test_files(dir: &Path, extension: &str) -> Vec<(String, PathBuf)> {
    let mut files: Vec<(String, PathBuf)> = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("failed to read test directory {}: {e}", dir.display()))
        .filter_map(|entry| {
            let entry = entry.ok()?;
            let path = entry.path();
            if path.extension()? == extension {
                let name = path.file_stem()?.to_str()?.to_string();
                Some((name, path))
            } else {
                None
            }
        })
        .collect();
    files.sort_by(|a, b| a.0.cmp(&b.0));
    files
}

// --- Subprocess protocol ---

/// Run a test in a child process with a timeout.
///
/// Like `run_test_subprocess`, but uses `spawn()` + polling so we can
/// kill the child if it exceeds `timeout`. Returns `timed_out: true`
/// when the child is killed.
pub fn run_test_subprocess_timed(name: &str, path: &Path, timeout: Duration) -> TestResult {
    let exe = std::env::current_exe().expect("failed to get current exe");
    let start = Instant::now();
    let mut child = std::process::Command::new(exe)
        .arg("--__run")
        .arg(name)
        .arg(path)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::null())
        .spawn()
        .expect("failed to spawn child process");

    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                let elapsed = start.elapsed();
                let mut stdout_buf = String::new();
                if let Some(mut stdout) = child.stdout.take() {
                    use std::io::Read;
                    let _ = stdout.read_to_string(&mut stdout_buf);
                }
                if !status.success() && stdout_buf.is_empty() {
                    return TestResult {
                        name: name.to_string(),
                        directives: vec![],
                        crashed: true,
                        timed_out: false,
                        elapsed,
                    };
                }
                let directives = parse_subprocess_output(&stdout_buf);
                return TestResult {
                    name: name.to_string(),
                    directives,
                    crashed: false,
                    timed_out: false,
                    elapsed,
                };
            }
            Ok(None) => {
                if start.elapsed() > timeout {
                    let _ = child.kill();
                    let _ = child.wait();
                    return TestResult {
                        name: name.to_string(),
                        directives: vec![],
                        crashed: false,
                        timed_out: true,
                        elapsed: start.elapsed(),
                    };
                }
                std::thread::sleep(Duration::from_millis(50));
            }
            Err(_) => {
                return TestResult {
                    name: name.to_string(),
                    directives: vec![],
                    crashed: true,
                    timed_out: false,
                    elapsed: start.elapsed(),
                };
            }
        }
    }
}

/// Parse the stdout protocol emitted by a child process.
/// Each line: `PASS|FAIL <index> <label>\t<error>`
pub fn parse_subprocess_output(stdout: &str) -> Vec<DirectiveResult> {
    stdout
        .lines()
        .filter_map(|line| {
            let (status, rest) = line.split_once(' ')?;
            let passed = status == "PASS";
            let (idx_str, rest) = rest.split_once(' ')?;
            let index: usize = idx_str.parse().ok()?;
            let (label, error) = if let Some((l, e)) = rest.split_once('\t') {
                (l.to_string(), if e.is_empty() { None } else { Some(e.to_string()) })
            } else {
                (rest.to_string(), None)
            };
            Some(DirectiveResult { index, passed, label, error })
        })
        .collect()
}

/// Print subprocess protocol lines for a set of directive results.
/// Call this from the child process entry point.
pub fn print_subprocess_results(results: &[DirectiveResult]) {
    for r in results {
        let status = if r.passed { "PASS" } else { "FAIL" };
        let error = r.error.as_deref().unwrap_or("");
        println!("{status} {} {}\t{error}", r.index, r.label);
    }
}

// --- Rendering ---

/// Render a Fira Code progress bar of given width (in characters).
/// Uses colored PUA glyphs: green for filled, red for empty.
pub fn render_bar(passed: usize, total: usize, width: usize) -> String {
    if width < 2 {
        return String::new();
    }
    let inner = width - 2;
    let filled = if total > 0 {
        (passed * inner + total / 2) / total
    } else {
        inner
    };
    let empty = inner - filled;

    let mut bar = String::new();

    if filled > 0 {
        bar.push_str(&format!("{GREEN}{BAR_LEFT_FILLED}{RESET}"));
    } else {
        bar.push_str(&format!("{RED}{BAR_LEFT_EMPTY}{RESET}"));
    }

    for _ in 0..filled {
        bar.push_str(&format!("{GREEN}{BAR_MID_FILLED}{RESET}"));
    }
    for _ in 0..empty {
        bar.push_str(&format!("{RED}{BAR_MID_EMPTY}{RESET}"));
    }

    if empty == 0 {
        bar.push_str(&format!("{GREEN}{BAR_RIGHT_FILLED}{RESET}"));
    } else {
        bar.push_str(&format!("{RED}{BAR_RIGHT_EMPTY}{RESET}"));
    }

    bar
}

// --- Box drawing helpers ---

fn pad_line(content: &str, display_width: usize, inner_width: usize) -> String {
    let pad = inner_width.saturating_sub(display_width);
    format!("│ {content}{} │", " ".repeat(pad))
}

fn border(left: char, right: char, inner_width: usize) -> String {
    format!("{left}{}{right}", "─".repeat(inner_width + 2))
}

/// Render a stats label line (e.g. "460 passed  3 failed").
fn render_stats_line(passed: usize, failed: usize, inner_width: usize) -> String {
    let stats_text = if failed > 0 {
        format!("{GREEN}{passed} passed{RESET}  {RED}{failed} failed{RESET}")
    } else {
        format!("{GREEN}{passed} passed{RESET}")
    };
    let stats_plain_len = if failed > 0 {
        format!("{passed} passed  {failed} failed").len()
    } else {
        format!("{passed} passed").len()
    };
    pad_line(&stats_text, stats_plain_len, inner_width)
}

/// Render error detail lines for a set of directive results, truncated to fit the box.
fn render_error_lines(
    results: &[DirectiveResult],
    max_errors: usize,
    inner_width: usize,
    indent: usize,
) -> String {
    let mut out = String::new();
    let failed_count = results.iter().filter(|r| !r.passed).count();
    let prefix = " ".repeat(indent);
    for r in results.iter().filter(|r| !r.passed).take(max_errors) {
        let err = r.error.as_deref().unwrap_or("unknown");
        let line = format!("#{}: {} - {err}", r.index + 1, r.label);
        let max_len = inner_width - indent;
        let truncated = if line.chars().count() > max_len {
            let t: String = line.chars().take(max_len - 1).collect();
            format!("{t}…")
        } else {
            line
        };
        let colored = format!("{RED}{truncated}{RESET}");
        out.push_str(&pad_line(
            &format!("{prefix}{colored}"),
            indent + truncated.len(),
            inner_width,
        ));
        out.push('\n');
    }
    let remaining = failed_count.saturating_sub(max_errors);
    if remaining > 0 {
        let more = format!("... and {remaining} more");
        let colored = format!("{DIM}{more}{RESET}");
        out.push_str(&pad_line(
            &format!("{prefix}{colored}"),
            indent + more.len(),
            inner_width,
        ));
        out.push('\n');
    }
    out
}

/// Render a boxed dot grid showing per-directive pass/fail with error details.
///
/// Used in detailed mode (single test).
pub fn render_dot_grid(name: &str, results: &[DirectiveResult]) -> String {
    let total = results.len();
    let passed = results.iter().filter(|r| r.passed).count();
    let failed = total - passed;
    let pct = if total > 0 {
        passed as f64 / total as f64 * 100.0
    } else {
        100.0
    };

    let cols = 60;
    let header_text = format!("{name}: {passed}/{total} passed ({pct:.1}%)");
    let header = format!("{BOLD}{header_text}{RESET}");
    let inner_width = 80.max(header_text.len());

    let mut out = String::new();
    out.push_str(&border('┌', '┐', inner_width));
    out.push('\n');
    out.push_str(&pad_line(&header, header_text.len(), inner_width));
    out.push('\n');
    out.push_str(&border('├', '┤', inner_width));
    out.push('\n');

    // Dot grid.
    for chunk in results.chunks(cols) {
        let mut row = String::new();
        for r in chunk {
            if r.passed {
                row.push_str(&format!("{GREEN}●{RESET}"));
            } else {
                row.push_str(&format!("{RED}○{RESET}"));
            }
        }
        out.push_str(&pad_line(&row, chunk.len(), inner_width));
        out.push('\n');
    }

    // Progress bar + stats.
    out.push_str(&border('├', '┤', inner_width));
    out.push('\n');
    out.push_str(&pad_line(
        &render_bar(passed, total, inner_width),
        inner_width,
        inner_width,
    ));
    out.push('\n');
    out.push_str(&render_stats_line(passed, failed, inner_width));
    out.push('\n');

    // Error details.
    if failed > 0 {
        out.push_str(&border('├', '┤', inner_width));
        out.push('\n');
        out.push_str(&render_error_lines(results, 10, inner_width, 0));
    }

    out.push_str(&border('└', '┘', inner_width));
    out
}

// --- Live TUI test runner ---

/// Status of a single test in the parallel runner.
pub enum TestStatus {
    Pending,
    Running { started: Instant },
    Completed(TestResult),
}

/// A test entry tracked by the parallel runner.
pub struct TestEntry {
    pub name: String,
    pub path: PathBuf,
    pub status: TestStatus,
}

/// Render a single entry row with the appropriate format for its status.
fn render_entry_row(entry: &TestEntry, name_width: usize, bar_width: usize) -> String {
    match &entry.status {
        TestStatus::Pending => {
            format!(
                "  {DIM}·{RESET} {DIM}{:<name_width$}{RESET}",
                entry.name,
            )
        }
        TestStatus::Running { started } => {
            let elapsed_str = format!("{:.1}s", started.elapsed().as_secs_f64());
            let bar = render_bar(0, 1, bar_width);
            format!(
                "  {DIM}⟳{RESET} {BOLD}{:<name_width$}{RESET}  {bar}  {DIM}...{RESET}      {DIM}{elapsed_str}{RESET}",
                entry.name,
            )
        }
        TestStatus::Completed(r) => {
            let (icon, stats) = if r.timed_out {
                (format!("{RED}⏱{RESET}"), format!("{RED}TIMED OUT{RESET}"))
            } else if r.crashed {
                (format!("{RED}!{RESET}"), format!("{RED}CRASHED{RESET}"))
            } else if r.is_fail() {
                let s = format!("{}/{}", r.passed(), r.total());
                (format!("{RED}✗{RESET}"), s)
            } else {
                let s = format!("{}/{}", r.passed(), r.total());
                (format!("{GREEN}✓{RESET}"), s)
            };

            let bar = if r.timed_out || r.crashed {
                render_bar(0, 1, bar_width)
            } else {
                render_bar(r.passed(), r.total(), bar_width)
            };

            let elapsed_str = format!("{:.1}s", r.elapsed.as_secs_f64());
            format!(
                "  {icon} {BOLD}{:<name_width$}{RESET}  {bar}  {stats}  {DIM}{elapsed_str}{RESET}",
                r.name,
            )
        }
    }
}

/// Compute the plain-text display width of an entry row (no ANSI escapes).
fn entry_row_plain_len(entry: &TestEntry, name_width: usize, bar_width: usize) -> usize {
    match &entry.status {
        TestStatus::Pending => {
            // "  · name"
            2 + 1 + 1 + name_width
        }
        TestStatus::Running { started } => {
            let elapsed_str = format!("{:.1}s", started.elapsed().as_secs_f64());
            // "  ⟳ name  bar  ...      elapsed"
            2 + 1 + 1 + name_width + 2 + bar_width + 2 + 3 + 6 + elapsed_str.len()
        }
        TestStatus::Completed(r) => {
            let stats_plain_len = if r.timed_out {
                9
            } else if r.crashed {
                7
            } else {
                format!("{}/{}", r.passed(), r.total()).len()
            };
            let elapsed_str = format!("{:.1}s", r.elapsed.as_secs_f64());
            2 + 1 + 1 + name_width + 2 + bar_width + 2 + stats_plain_len + 2 + elapsed_str.len()
        }
    }
}

// --- Live footer helpers ---

/// Render a live footer as a bordered box section showing running tests and progress.
/// Returns the footer string and how many lines it occupies.
fn render_footer(
    entries: &[TestEntry],
    completed: usize,
    total: usize,
    files_passed: usize,
    files_failed: usize,
    elapsed: Duration,
    inner_width: usize,
) -> (String, usize) {
    let mut lines = 0usize;
    let mut out = String::new();

    // Separator from the completed rows above.
    out.push_str(&border('├', '┤', inner_width));
    out.push('\n');
    lines += 1;

    // Show running tests.
    for e in entries {
        if let TestStatus::Running { started } = &e.status {
            let elapsed_str = format!("{:.1}s", started.elapsed().as_secs_f64());
            let text = format!("  {DIM}⟳ {}  {elapsed_str}{RESET}", e.name);
            let plain_len = 4 + e.name.len() + 2 + elapsed_str.len();
            out.push_str(&pad_line(&text, plain_len, inner_width));
            out.push('\n');
            lines += 1;
        }
    }

    // Progress summary line.
    let stats = if files_failed > 0 {
        format!("{GREEN}{files_passed} passed{RESET}  {RED}{files_failed} failed{RESET}")
    } else {
        format!("{GREEN}{files_passed} passed{RESET}")
    };
    let stats_plain = if files_failed > 0 {
        format!("{files_passed} passed  {files_failed} failed")
    } else {
        format!("{files_passed} passed")
    };
    let elapsed_str = format!("{:.1}s", elapsed.as_secs_f64());
    let summary = format!(
        "  {DIM}[{completed}/{total}]{RESET} {stats}  {DIM}{elapsed_str}{RESET}",
    );
    let summary_plain_len = format!("  [{completed}/{total}] ").len() + stats_plain.len() + 2 + elapsed_str.len();
    out.push_str(&pad_line(&summary, summary_plain_len, inner_width));
    out.push('\n');
    lines += 1;

    // Bottom border.
    out.push_str(&border('└', '┘', inner_width));
    lines += 1;

    (out, lines)
}

/// Erase N lines of footer content.
///
/// Assumes the cursor is at the end of the last line (no trailing newline).
/// Clears the current line, then moves up and clears each remaining line.
fn erase_lines(out: &mut impl Write, count: usize) {
    if count == 0 {
        return;
    }
    // Clear the line the cursor is currently on.
    let _ = write!(out, "\r\x1b[2K");
    // Move up and clear each remaining line.
    for _ in 1..count {
        let _ = write!(out, "\x1b[A\x1b[2K");
    }
    let _ = out.flush();
}

/// Print the bottom portion of the overview box: failing test names, summary,
/// progress bars, helper commands, and bottom border.
fn print_box_summary(
    out: &mut impl Write,
    title: &str,
    test_command: &str,
    results: &[TestResult],
    inner_width: usize,
) {
    let total_files = results.len();
    let files_passed = results.iter().filter(|r| !r.is_fail()).count();
    let files_failed = total_files - files_passed;
    let total_directives: usize = results.iter().map(|r| r.total()).sum();
    let total_passed: usize = results.iter().map(|r| r.passed()).sum();
    let total_failed = total_directives - total_passed;
    let pct = if total_files > 0 {
        files_passed as f64 / total_files as f64 * 100.0
    } else {
        100.0
    };

    // Failing test names (compact — just names, no individual assertions).
    let failing: Vec<&TestResult> = results.iter().filter(|r| r.is_fail()).collect();
    if !failing.is_empty() {
        let _ = writeln!(out, "{}", border('├', '┤', inner_width));

        let max_shown = 15;
        for r in failing.iter().take(max_shown) {
            let detail = if r.timed_out {
                format!("TIMED OUT ({:.1}s)", r.elapsed.as_secs_f64())
            } else if r.crashed {
                "CRASHED".to_string()
            } else {
                format!("{} failed", r.failed())
            };
            let line = format!("{} - {detail}", r.name);
            let colored = format!("{RED}{line}{RESET}");
            let _ = writeln!(out, "{}", pad_line(
                &format!("  {colored}"),
                2 + line.len(),
                inner_width,
            ));
        }
        let remaining = failing.len().saturating_sub(max_shown);
        if remaining > 0 {
            let more = format!("... and {remaining} more");
            let colored = format!("{DIM}{more}{RESET}");
            let _ = writeln!(out, "{}", pad_line(
                &format!("  {colored}"),
                2 + more.len(),
                inner_width,
            ));
        }
    }

    // Summary + progress bars.
    let _ = writeln!(out, "{}", border('├', '┤', inner_width));
    let summary_text = format!(
        "{title}: {files_passed}/{total_files} files passed ({pct:.1}%) \
         - {total_passed}/{total_directives} directives"
    );
    let summary = format!("{BOLD}{summary_text}{RESET}");
    let _ = writeln!(out, "{}", pad_line(&summary, summary_text.len(), inner_width));

    let _ = writeln!(out, "{}", pad_line(
        &render_bar(files_passed, total_files, inner_width),
        inner_width, inner_width,
    ));
    let _ = writeln!(out, "{}", render_stats_line(files_passed, files_failed, inner_width));

    let _ = writeln!(out, "{}", pad_line(
        &render_bar(total_passed, total_directives, inner_width),
        inner_width, inner_width,
    ));
    let _ = writeln!(out, "{}", render_stats_line(total_passed, total_failed, inner_width));

    // Helper commands.
    let _ = writeln!(out, "{}", border('├', '┤', inner_width));
    let cmd_header = format!("{DIM}Run a single test for details:{RESET}");
    let _ = writeln!(out, "{}", pad_line(&cmd_header, "Run a single test for details:".len(), inner_width));
    let cmd = format!("  {test_command} -- <name>");
    let _ = writeln!(out, "{}", pad_line(&cmd, cmd.len(), inner_width));

    let _ = writeln!(out, "{}", border('└', '┘', inner_width));
    let _ = out.flush();
}

/// Run tests in parallel with a live bordered display.
///
/// Prints a complete bordered box as tests run:
/// - Top border + header printed immediately
/// - Completed test rows stream inside the box as they finish
/// - TTY: a live footer section shows running tests (redrawn in-place)
/// - After all tests finish, prints failing names + summary bars + helper commands
///
/// `test_command` is the cargo command prefix shown in the helper section
/// (e.g. `"cargo test -p wust --test spec_tests"`).
pub fn run_tests_parallel(
    title: &str,
    test_command: &str,
    tests: Vec<(String, PathBuf)>,
    timeout: Duration,
    is_tty: bool,
) -> Vec<TestResult> {
    let total = tests.len();
    let inner_width: usize = 80;
    let bar_col_width: usize = 30;
    let name_width = tests.iter().map(|(n, _)| n.len()).max().unwrap_or(0);

    // Build shared state.
    let entries: Vec<TestEntry> = tests
        .into_iter()
        .map(|(name, path)| TestEntry {
            name,
            path,
            status: TestStatus::Pending,
        })
        .collect();
    let state = Arc::new(Mutex::new(entries));

    // Build work queue (indices into the entries vec).
    let queue: VecDeque<usize> = (0..total).collect();
    let queue = Arc::new(Mutex::new(queue));

    // Spawn worker threads.
    let num_workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4)
        .min(total);

    let mut handles = Vec::with_capacity(num_workers);
    for _ in 0..num_workers {
        let queue = Arc::clone(&queue);
        let state = Arc::clone(&state);
        let handle = std::thread::spawn(move || {
            loop {
                let idx = {
                    let mut q = queue.lock().unwrap();
                    q.pop_front()
                };
                let Some(idx) = idx else { break };

                let (name, path) = {
                    let mut entries = state.lock().unwrap();
                    let e = &mut entries[idx];
                    e.status = TestStatus::Running {
                        started: Instant::now(),
                    };
                    (e.name.clone(), e.path.clone())
                };

                let result = run_test_subprocess_timed(&name, &path, timeout);

                {
                    let mut entries = state.lock().unwrap();
                    entries[idx].status = TestStatus::Completed(result);
                }
            }
        });
        handles.push(handle);
    }

    // Print top border + header.
    let start = Instant::now();
    let mut stdout = std::io::stdout().lock();
    let header_text = format!("{title}");
    let header = format!("{BOLD}{header_text}{RESET}");
    let _ = writeln!(stdout, "{}", border('┌', '┐', inner_width));
    let _ = writeln!(stdout, "{}", pad_line(&header, header_text.len(), inner_width));
    let _ = writeln!(stdout, "{}", border('├', '┤', inner_width));
    let _ = stdout.flush();

    // Render loop on the main thread.
    let mut printed = vec![false; total];
    let mut footer_lines = 0usize;
    let mut completed = 0usize;
    let mut files_passed = 0usize;
    let mut files_failed = 0usize;

    loop {
        // Erase the previous footer (TTY only).
        if is_tty && footer_lines > 0 {
            erase_lines(&mut stdout, footer_lines);
            footer_lines = 0;
        }

        // Print any newly completed test rows.
        let all_done = {
            let entries = state.lock().unwrap();
            for (i, e) in entries.iter().enumerate() {
                if !printed[i] {
                    if let TestStatus::Completed(r) = &e.status {
                        let row = render_entry_row(e, name_width, bar_col_width);
                        let row_len = entry_row_plain_len(e, name_width, bar_col_width);
                        let _ = writeln!(stdout, "{}", pad_line(&row, row_len, inner_width));
                        printed[i] = true;
                        completed += 1;
                        if r.is_fail() {
                            files_failed += 1;
                        } else {
                            files_passed += 1;
                        }
                    }
                }
            }

            // Draw live footer (TTY only).
            if is_tty {
                let (footer, lines) = render_footer(
                    &entries, completed, total,
                    files_passed, files_failed, start.elapsed(),
                    inner_width,
                );
                let _ = write!(stdout, "{footer}");
                let _ = stdout.flush();
                footer_lines = lines;
            }

            entries
                .iter()
                .all(|e| matches!(e.status, TestStatus::Completed(_)))
        };

        if all_done {
            break;
        }
        std::thread::sleep(Duration::from_millis(250));
    }

    // Erase final footer.
    if is_tty && footer_lines > 0 {
        erase_lines(&mut stdout, footer_lines);
    }

    // Join all workers.
    for h in handles {
        let _ = h.join();
    }

    // Extract results in original order.
    let entries = Arc::try_unwrap(state)
        .unwrap_or_else(|_| panic!("workers should be done"))
        .into_inner()
        .unwrap();
    let results: Vec<TestResult> = entries
        .into_iter()
        .map(|e| match e.status {
            TestStatus::Completed(r) => r,
            _ => unreachable!("all tests should be completed"),
        })
        .collect();

    // Print box bottom: failing names + summary bars + helper commands.
    print_box_summary(&mut stdout, title, test_command, &results, inner_width);

    results
}
