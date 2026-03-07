//! Box-drawing renderers for function and block visualizations.
//!
//! Provides [`BlockBox`] (single-line border) and [`FunctionBox`] (double-line
//! border) for rendering structured debug output with nested box-table layouts.
//! These are general-purpose rendering primitives with no domain knowledge —
//! they just draw boxes, tables, and text.

use super::table::Table;
use crate::ir::block::BlockId;

/// A block visualization with single-line border (`┌──┐`).
///
/// Contains optional params/results headers and a columnar data table.
/// The block auto-sizes its border to fit the widest content line.
///
/// # Examples
///
/// ```
/// use autosynth_codegen::disasm::boxes::BlockBox;
/// use autosynth_codegen::disasm::table::{Table, Column, Row, Align};
/// use autosynth_codegen::ir::block::BlockId;
///
/// let block = BlockBox {
///     id: BlockId::User(6),
///     params: vec!["v4<i32>".into()],
///     results: vec!["v4<i32>".into(), "v5<i32>".into()],
///     table: Table { columns: vec![], rows: vec![] },
/// };
/// let lines = block.render();
/// assert!(lines[0].contains("U6"));
/// ```
pub struct BlockBox {
    /// The block identifier, displayed in the top border.
    pub id: BlockId,
    /// Parameter descriptions shown as a header row (e.g. `["v4<i32>"]`).
    pub params: Vec<String>,
    /// Result descriptions shown as a footer row (e.g. `["v4<i32>", "v5<i32>"]`).
    pub results: Vec<String>,
    /// The columnar data table rendered inside the block.
    pub table: Table,
}

impl BlockBox {
    /// Render the block to a list of lines (without trailing newlines).
    ///
    /// Layout:
    /// ```text
    /// ┌─ L6 ─────────────┐
    /// │ params: (v4<i32>) │
    /// │ ... table ...     │
    /// │ result: (v4<i32>) │
    /// └───────────────────┘
    /// ```
    pub fn render(&self) -> Vec<String> {
        let table_lines = self.table.render();
        let inner_width = self.compute_inner_width(&table_lines);
        let mut lines = Vec::new();

        lines.push(self.render_top_border(inner_width));
        if !self.params.is_empty() {
            lines.push(self.render_content_line(&self.format_params(), inner_width));
        }
        for tl in &table_lines {
            lines.push(self.render_content_line(tl, inner_width));
        }
        if !self.results.is_empty() {
            lines.push(self.render_content_line(&self.format_results(), inner_width));
        }
        lines.push(self.render_bottom_border(inner_width));
        lines
    }

    /// Compute the inner width (content area between `│` borders).
    ///
    /// Takes the maximum of all table lines, params line, and results line,
    /// plus 2 for padding (1 space each side).
    fn compute_inner_width(&self, table_lines: &[String]) -> usize {
        let label = format!(" {} ", self.id);
        let min_from_label = label.chars().count() + 2; // "─ {label} ─" needs room

        let max_table = table_lines
            .iter()
            .map(|l| l.chars().count())
            .max()
            .unwrap_or(0);

        let params_width = if self.params.is_empty() {
            0
        } else {
            self.format_params().chars().count() + 2
        };

        let results_width = if self.results.is_empty() {
            0
        } else {
            self.format_results().chars().count() + 2
        };

        max_table
            .max(params_width)
            .max(results_width)
            .max(min_from_label)
    }

    /// Render the top border: `┌─ L6 ─...─┐`
    fn render_top_border(&self, inner_width: usize) -> String {
        let label = format!(" {} ", self.id);
        let label_width = label.chars().count();
        let fill_count = inner_width.saturating_sub(label_width + 1); // 1 for leading ─
        let mut line = String::new();
        line.push('┌');
        line.push('─');
        line.push_str(&label);
        for _ in 0..fill_count {
            line.push('─');
        }
        line.push('┐');
        line
    }

    /// Render the bottom border: `└─...─┘`
    fn render_bottom_border(&self, inner_width: usize) -> String {
        let mut line = String::new();
        line.push('└');
        for _ in 0..inner_width {
            line.push('─');
        }
        line.push('┘');
        line
    }

    /// Render a content line padded to inner width: `│ {content}...padding... │`
    fn render_content_line(&self, content: &str, inner_width: usize) -> String {
        let content_width = content.chars().count();
        let padding = inner_width.saturating_sub(content_width);
        let mut line = String::new();
        line.push('│');
        line.push_str(content);
        for _ in 0..padding {
            line.push(' ');
        }
        line.push('│');
        line
    }

    /// Format the params header line.
    fn format_params(&self) -> String {
        format!(" params: ({}) ", self.params.join(", "))
    }

    /// Format the results footer line.
    fn format_results(&self) -> String {
        format!(" result: ({}) ", self.results.join(", "))
    }
}

/// A function visualization with double-line border (`╔══╗`).
///
/// Contains a function signature, global register assignments, and
/// one or more [`BlockBox`] visualizations nested inside.
///
/// # Examples
///
/// ```
/// use autosynth_codegen::disasm::boxes::{FunctionBox, BlockBox};
/// use autosynth_codegen::disasm::table::Table;
/// use autosynth_codegen::ir::block::BlockId;
///
/// let func = FunctionBox {
///     signature: "fib<0>(w9<i32>) -> w9<i32>".into(),
///     globals: vec![("g.lb".into(), "x29".into())],
///     blocks: vec![],
/// };
/// let output = func.render();
/// assert!(output.contains("fib<0>"));
/// ```
pub struct FunctionBox {
    /// Function signature displayed in the top border.
    pub signature: String,
    /// Global/implicit register assignments (e.g. `[("g.lb", "x29")]`).
    pub globals: Vec<(String, String)>,
    /// Block boxes nested inside the function.
    pub blocks: Vec<BlockBox>,
}

impl FunctionBox {
    /// Render the function box to a single string with embedded newlines.
    ///
    /// Layout:
    /// ```text
    /// ╔═ fib<0>(...) ═══════╗
    /// ║  g.lb = x29    ...  ║
    /// ║                     ║
    /// ║  ┌─ L6 ──────┐     ║
    /// ║  │ ...        │     ║
    /// ║  └────────────┘     ║
    /// ║                     ║
    /// ╚═════════════════════╝
    /// ```
    pub fn render(&self) -> String {
        let block_renders: Vec<Vec<String>> = self
            .blocks
            .iter()
            .map(|b| b.render())
            .collect();

        let inner_width = self.compute_inner_width(&block_renders);
        let mut lines = Vec::new();

        lines.push(self.render_top_border(inner_width));
        if !self.globals.is_empty() {
            lines.push(self.render_double_content_line(&self.format_globals(), inner_width));
        }
        lines.push(self.render_double_content_line("", inner_width));

        for (i, block_lines) in block_renders.iter().enumerate() {
            for bl in block_lines {
                let indented = format!("  {bl}");
                lines.push(self.render_double_content_line(&indented, inner_width));
            }
            if i + 1 < block_renders.len() {
                lines.push(self.render_double_content_line("", inner_width));
            }
        }

        if !block_renders.is_empty() {
            lines.push(self.render_double_content_line("", inner_width));
        }
        lines.push(self.render_bottom_border(inner_width));

        lines.join("\n")
    }

    /// Compute inner width for the function box.
    fn compute_inner_width(&self, block_renders: &[Vec<String>]) -> usize {
        let sig_label = format!(" {} ", self.signature);
        let min_from_sig = sig_label.chars().count() + 2;

        let globals_width = if self.globals.is_empty() {
            0
        } else {
            self.format_globals().chars().count() + 2
        };

        let max_block = block_renders
            .iter()
            .flat_map(|lines| lines.iter())
            .map(|l| l.chars().count() + 4) // 2 indent + 2 padding
            .max()
            .unwrap_or(0);

        min_from_sig.max(globals_width).max(max_block)
    }

    /// Render the top border: `╔═ signature ═...═╗`
    fn render_top_border(&self, inner_width: usize) -> String {
        let label = format!(" {} ", self.signature);
        let label_width = label.chars().count();
        let fill_count = inner_width.saturating_sub(label_width + 1);
        let mut line = String::new();
        line.push('╔');
        line.push('═');
        line.push_str(&label);
        for _ in 0..fill_count {
            line.push('═');
        }
        line.push('╗');
        line
    }

    /// Render the bottom border: `╚═...═╝`
    fn render_bottom_border(&self, inner_width: usize) -> String {
        let mut line = String::new();
        line.push('╚');
        for _ in 0..inner_width {
            line.push('═');
        }
        line.push('╝');
        line
    }

    /// Render a content line with double border: `║ {content}...padding... ║`
    fn render_double_content_line(&self, content: &str, inner_width: usize) -> String {
        let content_width = content.chars().count();
        let padding = inner_width.saturating_sub(content_width);
        let mut line = String::new();
        line.push('║');
        line.push_str(content);
        for _ in 0..padding {
            line.push(' ');
        }
        line.push('║');
        line
    }

    /// Format the globals line: `  g.lb = x29    g.fuel = x0    ...`
    fn format_globals(&self) -> String {
        let pairs: Vec<String> = self
            .globals
            .iter()
            .map(|(name, reg)| format!("{name} = {reg}"))
            .collect();
        format!("  {}", pairs.join("    "))
    }
}
