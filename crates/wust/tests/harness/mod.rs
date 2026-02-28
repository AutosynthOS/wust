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

use std::path::{Path, PathBuf};

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
        self.crashed || self.failed() > 0
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

/// Run a test in a child process to isolate segfaults.
///
/// Re-invokes the current binary with `--__run <name> <path>`.
/// The child should print lines of `PASS|FAIL <index> <label>\t<error>` to stdout
/// and exit 0 (all pass) or 1 (some fail). A crash (signal kill, empty stdout)
/// is reported as `TestResult { crashed: true }`.
pub fn run_test_subprocess(name: &str, path: &Path) -> TestResult {
    let exe = std::env::current_exe().expect("failed to get current exe");
    let output = std::process::Command::new(exe)
        .arg("--__run")
        .arg(name)
        .arg(path)
        .output()
        .expect("failed to spawn child process");

    if !output.status.success() && output.stdout.is_empty() {
        return TestResult {
            name: name.to_string(),
            directives: vec![],
            crashed: true,
        };
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    let directives = parse_subprocess_output(&stdout);

    TestResult {
        name: name.to_string(),
        directives,
        crashed: false,
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

/// Render the overview box containing all test results in a single bordered table.
///
/// Used in overview mode (multiple tests). Each test is one row with
/// name, mini progress bar, and pass/fail count. Failed tests show
/// error details. A combined progress bar sits at the bottom.
pub fn render_overview(title: &str, results: &[TestResult]) -> String {
    let inner_width: usize = 80;
    let name_width = results.iter().map(|r| r.name.len()).max().unwrap_or(0);
    let bar_col_width: usize = 30;

    let total_files = results.len();
    let files_passed = results.iter().filter(|r| !r.is_fail()).count();
    let files_failed = total_files - files_passed;
    let total_directives: usize = results.iter().map(|r| r.total()).sum();
    let total_passed: usize = results.iter().map(|r| r.passed()).sum();
    let pct = if total_files > 0 {
        files_passed as f64 / total_files as f64 * 100.0
    } else {
        100.0
    };

    let mut out = String::new();

    // Header.
    out.push_str(&border('┌', '┐', inner_width));
    out.push('\n');
    let header_text = format!(
        "{title}: {files_passed}/{total_files} files passed ({pct:.1}%) \
         - {total_passed}/{total_directives} directives"
    );
    let header = format!("{BOLD}{header_text}{RESET}");
    out.push_str(&pad_line(&header, header_text.len(), inner_width));
    out.push('\n');
    out.push_str(&border('├', '┤', inner_width));
    out.push('\n');

    // One row per test.
    for r in results {
        let passed = r.passed();
        let total = r.total();

        let (icon, stats) = if r.crashed {
            (format!("{RED}!{RESET}"), format!("{RED}CRASHED{RESET}"))
        } else if r.is_fail() {
            (format!("{RED}✗{RESET}"), format!("{passed}/{total}"))
        } else {
            (format!("{GREEN}✓{RESET}"), format!("{passed}/{total}"))
        };

        let bar = if r.crashed {
            render_bar(0, 1, bar_col_width)
        } else {
            render_bar(passed, total, bar_col_width)
        };

        let stats_plain_len = if r.crashed { 7 } else { stats.len() };
        let row_text_width = 2 + 1 + 1 + name_width + 2 + bar_col_width + 2 + stats_plain_len;
        let row = format!(
            "  {icon} {BOLD}{:<name_width$}{RESET}  {bar}  {stats}",
            r.name,
        );
        out.push_str(&pad_line(&row, row_text_width, inner_width));
        out.push('\n');
    }

    // Error details for failing tests.
    let failing_tests: Vec<&TestResult> = results.iter().filter(|r| r.is_fail()).collect();
    if !failing_tests.is_empty() {
        out.push_str(&border('├', '┤', inner_width));
        out.push('\n');
        let max_failing_tests = 10;
        for r in failing_tests.iter().take(max_failing_tests) {
            if r.crashed {
                let header_line = format!("{} (CRASHED - segfault or signal):", r.name);
                let colored_header = format!("{RED}{BOLD}{header_line}{RESET}");
                out.push_str(&pad_line(
                    &format!("  {colored_header}"),
                    2 + header_line.len(),
                    inner_width,
                ));
                out.push('\n');
                continue;
            }
            let header_line = format!("{} ({} failed):", r.name, r.failed());
            let colored_header = format!("{RED}{BOLD}{header_line}{RESET}");
            out.push_str(&pad_line(
                &format!("  {colored_header}"),
                2 + header_line.len(),
                inner_width,
            ));
            out.push('\n');
            out.push_str(&render_error_lines(&r.directives, 3, inner_width, 4));
        }
        let remaining_tests = failing_tests.len().saturating_sub(max_failing_tests);
        if remaining_tests > 0 {
            let more = format!("... and {remaining_tests} more failing tests");
            let colored = format!("{DIM}{more}{RESET}");
            out.push_str(&pad_line(
                &format!("  {colored}"),
                2 + more.len(),
                inner_width,
            ));
            out.push('\n');
        }
    }

    // File-level progress bar.
    out.push_str(&border('├', '┤', inner_width));
    out.push('\n');
    let files_label = format!("{DIM}files{RESET}");
    let files_label_plain = "files";
    out.push_str(&pad_line(&files_label, files_label_plain.len(), inner_width));
    out.push('\n');
    out.push_str(&pad_line(
        &render_bar(files_passed, total_files, inner_width),
        inner_width,
        inner_width,
    ));
    out.push('\n');
    out.push_str(&render_stats_line(files_passed, files_failed, inner_width));
    out.push('\n');

    // Directive-level progress bar.
    let total_failed = total_directives - total_passed;
    let dir_label = format!("{DIM}directives{RESET}");
    let dir_label_plain = "directives";
    out.push_str(&pad_line(&dir_label, dir_label_plain.len(), inner_width));
    out.push('\n');
    out.push_str(&pad_line(
        &render_bar(total_passed, total_directives, inner_width),
        inner_width,
        inner_width,
    ));
    out.push('\n');
    out.push_str(&render_stats_line(total_passed, total_failed, inner_width));
    out.push('\n');

    out.push_str(&border('└', '┘', inner_width));
    out
}
