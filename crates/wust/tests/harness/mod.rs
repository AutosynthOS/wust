//! Reusable test harness with parallel execution, subprocess isolation,
//! live TUI output, and colored progress bars.
//!
//! See `tests/harness/HARNESS.md` for full documentation: CLI flags,
//! display modes, subprocess protocol, and API reference.
//!
//! **NOTE to agents:** If you add, remove, or change any public API,
//! CLI flags, display modes, or behavior in this module, you MUST
//! update `HARNESS.md` in this directory to reflect the changes.

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
pub const CYAN: &str = "\x1b[36m";
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
    /// 1-indexed line number in the source file where the directive starts.
    pub line: Option<usize>,
    /// Source text of the directive (e.g. the full s-expression).
    pub source: Option<String>,
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
    pub verbose: bool,
}

pub fn parse_cli_args() -> CliArgs {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut filter = None;
    let mut exact = false;
    let mut skip = vec![];
    let mut list = false;
    let mut expand = false;
    let mut verbose = false;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--exact" => exact = true,
            "--list" => list = true,
            "--expand" => expand = true,
            "--verbose" | "-v" => verbose = true,
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
    CliArgs {
        filter,
        exact,
        skip,
        list,
        expand,
        verbose,
    }
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
/// Spawns the child, drains stdout on a background thread (to prevent
/// pipe-buffer deadlocks when the child produces large output), and
/// polls `try_wait` for completion or timeout.
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

    // Drain stdout on a background thread so the pipe buffer never fills
    // up and blocks the child. Without this, tests producing >64KB of
    // output (e.g. 2400+ failing assertions) would deadlock.
    let stdout = child.stdout.take().expect("stdout was piped");
    let reader = std::thread::spawn(move || {
        use std::io::Read;
        let mut buf = String::new();
        let mut stdout = stdout;
        let _ = stdout.read_to_string(&mut buf);
        buf
    });

    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                let elapsed = start.elapsed();
                let stdout_buf = reader.join().unwrap_or_default();
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
                    // Reader thread will see EOF after kill.
                    let _ = reader.join();
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
                let _ = reader.join();
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
/// Each line: `PASS|FAIL <index> <label>\t<error>\t<line>\t<source>`
pub fn parse_subprocess_output(stdout: &str) -> Vec<DirectiveResult> {
    stdout
        .lines()
        .filter_map(|line| {
            let (status, rest) = line.split_once(' ')?;
            let passed = status == "PASS";
            let (idx_str, rest) = rest.split_once(' ')?;
            let index: usize = idx_str.parse().ok()?;
            // Split on tabs: label \t error \t line \t source
            let parts: Vec<&str> = rest.splitn(4, '\t').collect();
            let label = parts.first().unwrap_or(&"").to_string();
            let error = parts.get(1).and_then(|s| {
                if s.is_empty() { None } else { Some(s.to_string()) }
            });
            let line_num = parts.get(2).and_then(|s| s.parse::<usize>().ok());
            let source = parts.get(3).and_then(|s| {
                if s.is_empty() {
                    None
                } else {
                    Some(s.replace("\\n", "\n"))
                }
            });
            Some(DirectiveResult {
                index,
                passed,
                label,
                error,
                line: line_num,
                source,
            })
        })
        .collect()
}

/// Print subprocess protocol lines for a set of directive results.
/// Call this from the child process entry point.
pub fn print_subprocess_results(results: &[DirectiveResult]) {
    for r in results {
        let status = if r.passed { "PASS" } else { "FAIL" };
        let error = r.error.as_deref().unwrap_or("");
        let line = r.line.map(|l| l.to_string()).unwrap_or_default();
        // Escape newlines in source so the protocol stays one-line-per-result.
        let source = r
            .source
            .as_deref()
            .map(|s| s.replace('\n', "\\n"))
            .unwrap_or_default();
        println!("{status} {} {}\t{error}\t{line}\t{source}", r.index, r.label);
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

/// Render a three-state Fira Code progress bar: green (passed), red (failed),
/// dim (pending). Used in the live footer to show progress as tests complete.
fn render_bar_three(passed: usize, failed: usize, total: usize, width: usize) -> String {
    if width < 2 {
        return String::new();
    }
    let inner = width - 2;
    let (p, f) = if total > 0 {
        let p = (passed * inner + total / 2) / total;
        let f = (failed * inner + total / 2) / total;
        // Clamp so p + f doesn't exceed inner.
        let f = f.min(inner - p);
        (p, f)
    } else {
        (inner, 0)
    };
    let pending = inner - p - f;

    let mut bar = String::new();

    // Left cap.
    if p > 0 {
        bar.push_str(&format!("{GREEN}{BAR_LEFT_FILLED}{RESET}"));
    } else if f > 0 {
        bar.push_str(&format!("{RED}{BAR_LEFT_FILLED}{RESET}"));
    } else {
        bar.push_str(&format!("{DIM}{BAR_LEFT_EMPTY}{RESET}"));
    }

    // Green (passed) segment.
    for _ in 0..p {
        bar.push_str(&format!("{GREEN}{BAR_MID_FILLED}{RESET}"));
    }
    // Red (failed) segment.
    for _ in 0..f {
        bar.push_str(&format!("{RED}{BAR_MID_FILLED}{RESET}"));
    }
    // Dim (pending) segment.
    for _ in 0..pending {
        bar.push_str(&format!("{DIM}{BAR_MID_EMPTY}{RESET}"));
    }

    // Right cap.
    if pending > 0 {
        bar.push_str(&format!("{DIM}{BAR_RIGHT_EMPTY}{RESET}"));
    } else if f > 0 {
        bar.push_str(&format!("{RED}{BAR_RIGHT_FILLED}{RESET}"));
    } else {
        bar.push_str(&format!("{GREEN}{BAR_RIGHT_FILLED}{RESET}"));
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

/// Render a stats label with passed, failed, and optional pending counts.
fn render_stats_line_three(
    passed: usize,
    failed: usize,
    pending: usize,
    inner_width: usize,
) -> String {
    let mut text = format!("{GREEN}{passed} passed{RESET}");
    let mut plain = format!("{passed} passed");
    if failed > 0 {
        text.push_str(&format!("  {RED}{failed} failed{RESET}"));
        plain.push_str(&format!("  {failed} failed"));
    }
    if pending > 0 {
        text.push_str(&format!("  {DIM}{pending} pending{RESET}"));
        plain.push_str(&format!("  {pending} pending"));
    }
    pad_line(&text, plain.len(), inner_width)
}

/// Render a single error in diagnostic style inside an inner box.
///
/// Layout for each error:
/// ```text
/// │ #12: assert_return(block-param) - got [I32(5)], expected [I32(6)]      │
/// │                                                                        │
/// │   142 │ (assert_return (invoke "block-param" (i32.const 5)) ...)       │
/// │       │  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^        │
/// ```
fn render_error_diagnostic(
    r: &DirectiveResult,
    detail_width: usize,
    inner_line: &dyn Fn(&str, usize) -> String,
    out: &mut String,
) {
    // Combined header: "#N: label - error" on one line, wrapped if needed.
    let idx_str = format!("#{}: ", r.index + 1);
    let err = r.error.as_deref().unwrap_or("unknown");
    let separator = " - ";
    let full_plain = format!("{idx_str}{}{separator}{err}", r.label);

    if full_plain.len() <= detail_width {
        // Fits on one line.
        let colored = format!(
            "{DIM}{idx_str}{RESET}{}{RED}{separator}{err}{RESET}",
            r.label,
        );
        out.push_str(&inner_line(&colored, full_plain.len()));
        out.push('\n');
    } else {
        // Wrap: first line gets as much as fits, continuation lines
        // are indented and show the rest of the error in red.
        let first_part = format!("{idx_str}{}{separator}", r.label);
        let err_budget = detail_width.saturating_sub(first_part.len());
        let err_lines = wrap_text(err, err_budget.max(1));
        // First line: header + first chunk of error.
        let first_err = err_lines.first().map(|s| s.as_str()).unwrap_or("");
        let colored_first = format!(
            "{DIM}{idx_str}{RESET}{}{RED}{separator}{first_err}{RESET}",
            r.label,
        );
        let first_plain_len = first_part.len() + first_err.len();
        out.push_str(&inner_line(&colored_first, first_plain_len));
        out.push('\n');
        // Continuation lines: indented under the error.
        let indent = first_part.len().min(detail_width / 3);
        let cont_budget = detail_width.saturating_sub(indent);
        // Re-wrap remaining error text at the continuation width.
        let remaining_err = if err.len() > err_budget && err_budget > 0 {
            err[err_budget..].trim_start()
        } else {
            ""
        };
        for line in wrap_text(remaining_err, cont_budget) {
            let prefix = " ".repeat(indent);
            let plain_len = indent + line.len();
            let colored = format!("{RED}{line}{RESET}");
            out.push_str(&inner_line(
                &format!("{prefix}{colored}"),
                plain_len,
            ));
            out.push('\n');
        }
    }

    // Source snippet (if available).
    if let Some(src) = &r.source {
        let line_num = r.line.unwrap_or(0);
        out.push_str(&inner_line("", 0));
        out.push('\n');

        // gutter_width: number of digits for the largest line number.
        let gutter_digits = format!("{}", line_num + src.lines().count()).len();
        // Display width of the gutter: digits + " │ " (3 display chars).
        let gutter_display = gutter_digits + 3;
        for (i, src_line) in src.lines().enumerate() {
            let ln = line_num + i;
            let gutter = format!("{:>w$} │ ", ln, w = gutter_digits);
            let budget = detail_width.saturating_sub(gutter_display);
            let trimmed = truncate_str(src_line, budget);
            let plain_len = gutter_display + trimmed.len();
            let colored = format!(
                "{DIM}{gutter}{RESET}{CYAN}{trimmed}{RESET}",
            );
            out.push_str(&inner_line(&colored, plain_len));
            out.push('\n');

            // Underline on the first line.
            if i == 0 {
                let content_start = src_line
                    .find(|c: char| !c.is_whitespace())
                    .unwrap_or(0);
                let content_len = src_line.len().saturating_sub(content_start);
                let caret_len = content_len.min(budget.saturating_sub(content_start));
                let underline = format!(
                    "{}{}",
                    " ".repeat(content_start),
                    "^".repeat(caret_len),
                );
                let underline_gutter = format!(
                    "{:>w$} │ ", "", w = gutter_digits,
                );
                let underline_plain_len = gutter_display + content_start + caret_len;
                let colored_underline = format!(
                    "{DIM}{underline_gutter}{RESET}{RED}{underline}{RESET}",
                );
                out.push_str(&inner_line(&colored_underline, underline_plain_len));
                out.push('\n');
            }
        }
    }
}

/// Truncate a string to fit within `max_len` characters.
fn truncate_str(s: &str, max_len: usize) -> String {
    if s.len() <= max_len {
        s.to_string()
    } else if max_len > 1 {
        format!("{}…", &s[..max_len - 1])
    } else {
        String::new()
    }
}

/// Wrap text into lines that fit within `max_width` characters.
fn wrap_text(text: &str, max_width: usize) -> Vec<String> {
    if max_width == 0 {
        return vec![];
    }
    let mut lines = Vec::new();
    let mut remaining = text;
    while remaining.len() > max_width {
        // Try to break at a space.
        let break_at = remaining[..max_width]
            .rfind(' ')
            .unwrap_or(max_width);
        let break_at = if break_at == 0 { max_width } else { break_at };
        lines.push(remaining[..break_at].to_string());
        remaining = remaining[break_at..].trim_start();
    }
    if !remaining.is_empty() {
        lines.push(remaining.to_string());
    }
    lines
}

/// Render a complete inner box for a test in detailed/expand mode.
///
/// Layout:
/// ```text
/// │ ┌──────────────────────────────────────────────────┐ │
/// │ │  ✗ name                           25/50  0.1s    │ │
/// │ ├──────────────────────────────────────────────────┤ │
/// │ │ ●●○○○○●●●●●●○○●●●●●●○○                           │ │
/// │ │ ████████████░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░ │ │
/// │ │ 25 passed  25 failed                             │ │
/// │ ├──────────────────────────────────────────────────┤ │  (only if errors)
/// │ │   #3: assert_return(...) - error message         │ │
/// │ └──────────────────────────────────────────────────┘ │
/// ```
fn render_detail_box(
    entry: &TestEntry,
    name_width: usize,
    inner_width: usize,
    verbose: bool,
) -> String {
    let result = match &entry.status {
        TestStatus::Completed(r) => r,
        _ => return String::new(),
    };

    let total = result.total();
    let passed = result.passed();
    let failed = total - passed;
    // Inner box content width: inner_width minus inner │ + space on each side.
    let detail_width = inner_width - 4;

    let mut out = String::new();

    // Helper: wrap content in inner box borders, then in outer box borders.
    let inner_line = |content: &str, display_width: usize| -> String {
        let ipad = detail_width.saturating_sub(display_width);
        let inner = format!("│ {content}{} │", " ".repeat(ipad));
        pad_line(&inner, inner_width, inner_width)
    };

    let inner_border = |left: char, right: char| -> String {
        let inner = format!("{left}{}{right}", "─".repeat(inner_width - 2));
        pad_line(&inner, inner_width, inner_width)
    };

    // Inner box top border.
    out.push_str(&inner_border('┌', '┐'));
    out.push('\n');

    // Header row: icon + name + bar + stats + elapsed (inside inner box).
    let (header, header_len) = render_entry_row(entry, name_width, detail_width);
    out.push_str(&inner_line(&header, header_len));
    out.push('\n');

    if !result.timed_out && !result.crashed {
        // Separator between header and dot grid.
        out.push_str(&inner_border('├', '┤'));
        out.push('\n');
        // Dot grid — uses full detail_width for columns.
        for chunk in result.directives.chunks(detail_width) {
            let mut row = String::new();
            for r in chunk {
                if r.passed {
                    row.push_str(&format!("{GREEN}●{RESET}"));
                } else {
                    row.push_str(&format!("{RED}○{RESET}"));
                }
            }
            out.push_str(&inner_line(&row, chunk.len()));
            out.push('\n');
        }

        // Stats line.
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
        out.push_str(&inner_line(&stats_text, stats_plain_len));
        out.push('\n');

        // Error details — each error gets its own separated section
        // with source snippet and diagnostic-style formatting.
        if failed > 0 {
            let max_errors = if verbose { usize::MAX } else { 6 };
            let failing: Vec<_> = result
                .directives
                .iter()
                .filter(|r| !r.passed)
                .collect();
            for r in failing.iter().take(max_errors) {
                out.push_str(&inner_border('├', '┤'));
                out.push('\n');
                render_error_diagnostic(
                    r, detail_width, &inner_line, &mut out,
                );
            }
            let remaining = failing.len().saturating_sub(max_errors);
            if remaining > 0 {
                out.push_str(&inner_border('├', '┤'));
                out.push('\n');
                let hint = format!(
                    "... and {remaining} more (use --verbose to show all)"
                );
                let colored = format!("{DIM}{hint}{RESET}");
                out.push_str(&inner_line(&colored, hint.len()));
                out.push('\n');
            }
        }
    }

    // Inner box bottom border.
    out.push_str(&inner_border('└', '┘'));
    out.push('\n');

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

// Table column widths for entry rows.
const STATS_COL: usize = 9; // fits "TIMEOUT", "CRASHED", "2514/2514"
const TIME_COL: usize = 5;  // fits "99.9s"

/// Compute the bar width for a given available width and name width.
fn bar_width_for(avail_width: usize, name_width: usize) -> usize {
    // Layout: " X name  bar  stats  time"
    //          1 1 1nw 2    2  9   2  5  = nw + 23
    avail_width.saturating_sub(name_width + 23).max(10)
}

/// Render a single entry row with table-aligned columns.
///
/// Returns `(rendered_string, plain_display_width)`.
/// Columns: icon+name | bar (flexible) | stats (right-aligned) | time (right-aligned)
fn render_entry_row(
    entry: &TestEntry,
    name_width: usize,
    avail_width: usize,
) -> (String, usize) {
    let bw = bar_width_for(avail_width, name_width);

    match &entry.status {
        TestStatus::Pending => {
            let row = format!(
                " {DIM}·{RESET} {DIM}{:<nw$}{RESET}",
                entry.name,
                nw = name_width,
            );
            (row, 1 + 1 + 1 + name_width)
        }
        TestStatus::Running { started } => {
            let elapsed_val = format!("{:.1}s", started.elapsed().as_secs_f64());
            let bar = render_bar(0, 1, bw);
            let stats_pad = format!("{:>w$}", "...", w = STATS_COL);
            let time_pad = format!("{:>w$}", elapsed_val, w = TIME_COL);
            let row = format!(
                " {DIM}⟳{RESET} {BOLD}{:<nw$}{RESET}  {bar}  {DIM}{stats_pad}{RESET}  {DIM}{time_pad}{RESET}",
                entry.name,
                nw = name_width,
            );
            (row, avail_width)
        }
        TestStatus::Completed(r) => {
            let (icon, stats_plain) = if r.timed_out {
                (format!("{RED}⏱{RESET}"), "TIMEOUT".to_string())
            } else if r.crashed {
                (format!("{RED}!{RESET}"), "CRASHED".to_string())
            } else if r.is_fail() {
                (format!("{RED}✗{RESET}"), format!("{}/{}", r.passed(), r.total()))
            } else {
                (format!("{GREEN}✓{RESET}"), format!("{}/{}", r.passed(), r.total()))
            };

            let bar = if r.timed_out || r.crashed {
                render_bar(0, 1, bw)
            } else {
                render_bar(r.passed(), r.total(), bw)
            };

            let elapsed_val = format!("{:.1}s", r.elapsed.as_secs_f64());
            let stats_pad = format!("{:>w$}", stats_plain, w = STATS_COL);
            let time_pad = format!("{:>w$}", elapsed_val, w = TIME_COL);

            let stats_colored = if r.timed_out || r.crashed || r.is_fail() {
                format!("{RED}{stats_pad}{RESET}")
            } else {
                stats_pad.clone()
            };

            let row = format!(
                " {icon} {BOLD}{:<nw$}{RESET}  {bar}  {stats_colored}  {DIM}{time_pad}{RESET}",
                r.name,
                nw = name_width,
            );
            (row, avail_width)
        }
    }
}

// --- Live footer helpers ---

/// Render a live footer as a bordered box section showing running tests,
/// progress bars, and summary stats. Returns the footer string and line count.
fn render_footer(
    title: &str,
    entries: &[TestEntry],
    completed: usize,
    total_files: usize,
    files_passed: usize,
    files_failed: usize,
    dir_passed: usize,
    dir_failed: usize,
    dir_total: usize,
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

    // Separator between running tests and summary.
    out.push_str(&border('├', '┤', inner_width));
    out.push('\n');
    lines += 1;

    // Summary + progress bars (shared renderer).
    let summary = render_summary_lines(
        title,
        completed,
        total_files,
        files_passed,
        files_failed,
        dir_passed,
        dir_failed,
        dir_total,
        elapsed,
        inner_width,
    );
    lines += summary.lines().count();
    out.push_str(&summary);

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

/// Render the summary section: header line, files bar + stats, directives bar + stats.
/// Shared between the live footer and the final box summary.
fn render_summary_lines(
    title: &str,
    completed: usize,
    total_files: usize,
    files_passed: usize,
    files_failed: usize,
    dir_passed: usize,
    dir_failed: usize,
    dir_total: usize,
    elapsed: Duration,
    inner_width: usize,
) -> String {
    let mut out = String::new();
    let files_pending = total_files - files_passed - files_failed;
    let elapsed_str = format!("{:.2}s", elapsed.as_secs_f64());
    let pct = if total_files > 0 {
        files_passed as f64 / total_files as f64 * 100.0
    } else {
        0.0
    };

    // Summary header line.
    let summary_text = format!(
        "{title}: [{completed}/{total_files}] {files_passed} passed ({pct:.0}%) \
         - {dir_passed}/{dir_total} directives  {elapsed_str}"
    );
    let summary = format!("{BOLD}{summary_text}{RESET}");
    out.push_str(&pad_line(&summary, summary_text.len(), inner_width));
    out.push('\n');

    // Files progress bar + stats.
    let files_bar = render_bar_three(files_passed, files_failed, total_files, inner_width);
    out.push_str(&pad_line(&files_bar, inner_width, inner_width));
    out.push('\n');
    out.push_str(&render_stats_line_three(
        files_passed,
        files_failed,
        files_pending,
        inner_width,
    ));
    out.push('\n');

    // Directives progress bar + stats.
    if dir_total > 0 {
        let dir_pending = dir_total - dir_passed - dir_failed;
        let dir_bar = render_bar_three(dir_passed, dir_failed, dir_total, inner_width);
        out.push_str(&pad_line(&dir_bar, inner_width, inner_width));
        out.push('\n');
        out.push_str(&render_stats_line_three(
            dir_passed,
            dir_failed,
            dir_pending,
            inner_width,
        ));
        out.push('\n');
    }

    out
}

/// Print the bottom portion of the overview box: failing test names, summary,
/// progress bars, and bottom border.
fn print_box_summary(
    out: &mut impl Write,
    title: &str,
    results: &[TestResult],
    elapsed: Duration,
    inner_width: usize,
) {
    let total_files = results.len();
    let files_passed = results.iter().filter(|r| !r.is_fail()).count();
    let files_failed = total_files - files_passed;
    let dir_total: usize = results.iter().map(|r| r.total()).sum();
    let dir_passed: usize = results.iter().map(|r| r.passed()).sum();
    let dir_failed = dir_total - dir_passed;

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
            let _ = writeln!(
                out,
                "{}",
                pad_line(&format!("  {colored}"), 2 + line.len(), inner_width,)
            );
        }
        let remaining = failing.len().saturating_sub(max_shown);
        if remaining > 0 {
            let more = format!("... and {remaining} more");
            let colored = format!("{DIM}{more}{RESET}");
            let _ = writeln!(
                out,
                "{}",
                pad_line(&format!("  {colored}"), 2 + more.len(), inner_width,)
            );
        }
    }

    // Summary + progress bars (shared renderer).
    let _ = writeln!(out, "{}", border('├', '┤', inner_width));
    let _ = write!(
        out,
        "{}",
        render_summary_lines(
            title,
            total_files,
            total_files,
            files_passed,
            files_failed,
            dir_passed,
            dir_failed,
            dir_total,
            elapsed,
            inner_width,
        )
    );

    let _ = writeln!(out, "{}", border('└', '┘', inner_width));
    let _ = out.flush();
}

/// Run tests in parallel with a live bordered display.
///
/// Prints a complete bordered box as tests run:
/// - Top border + header printed immediately
/// - Completed test rows stream inside the box as they finish
/// - TTY: a live footer section shows running tests (redrawn in-place)
/// - After all tests finish, prints failing names + summary bars
///
/// When `detailed` is true, each completed test also shows the dot grid
/// and error details inline (expand mode).
pub fn run_tests_parallel(
    title: &str,
    tests: Vec<(String, PathBuf)>,
    timeout: Duration,
    is_tty: bool,
    detailed: bool,
    verbose: bool,
) -> Vec<TestResult> {
    let total = tests.len();
    let inner_width: usize = 80;
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
    let _ = writeln!(
        stdout,
        "{}",
        pad_line(&header, header_text.len(), inner_width)
    );
    let _ = writeln!(stdout, "{}", border('├', '┤', inner_width));
    let _ = stdout.flush();

    // Render loop on the main thread.
    let mut printed = vec![false; total];
    let mut footer_lines = 0usize;
    let mut completed = 0usize;
    let mut files_passed = 0usize;
    let mut files_failed = 0usize;
    let mut dir_passed = 0usize;
    let mut dir_failed = 0usize;
    let mut dir_total = 0usize;

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
                        if detailed {
                            let box_str =
                                render_detail_box(e, name_width, inner_width, verbose);
                            let _ = write!(stdout, "{box_str}");
                        } else {
                            let (row, row_len) = render_entry_row(e, name_width, inner_width);
                            let _ = writeln!(stdout, "{}", pad_line(&row, row_len, inner_width));
                        }
                        printed[i] = true;
                        completed += 1;
                        dir_passed += r.passed();
                        dir_failed += r.failed();
                        dir_total += r.total();
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
                    title,
                    &entries,
                    completed,
                    total,
                    files_passed,
                    files_failed,
                    dir_passed,
                    dir_failed,
                    dir_total,
                    start.elapsed(),
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

    // Print box bottom: failing names + summary bars.
    print_box_summary(&mut stdout, title, &results, start.elapsed(), inner_width);

    // Final newline so the shell prompt doesn't overlap the box.
    let _ = writeln!(stdout);

    // In non-TTY (CI) mode, exit 1 on failure so CI detects it.
    // In TTY (interactive) mode, exit 0 for clean output.
    let any_failed = results.iter().any(|r| r.is_fail());
    if any_failed && !is_tty {
        std::process::exit(1);
    }

    results
}
