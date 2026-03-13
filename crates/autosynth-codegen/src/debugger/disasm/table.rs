//! Column-aligned table renderer with sparse cells.
//!
//! Renders a table with auto-sized columns separated by `│`, using
//! box-drawing characters for header/footer separators. Cells can be
//! `None` (sparse) to visually group multi-row expansions.
//!

/// Column text alignment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Align {
    /// Left-align cell content (pad on the right).
    Left,
    /// Right-align cell content (pad on the left).
    Right,
}

/// A single column definition.
#[derive(Debug, Clone)]
pub struct Column {
    /// Header text displayed in the separator row.
    pub header: String,
    /// Text alignment for cells in this column.
    pub align: Align,
}

/// A single row with optional (sparse) cells.
///
/// `None` cells render as blank space, used to visually group
/// multi-instruction expansions under a single wasm opcode.
#[derive(Debug, Clone)]
pub struct Row {
    /// One cell per column. `None` means this cell is empty (sparse).
    pub cells: Vec<Option<String>>,
}

/// A column-aligned table with box-drawing separators.
///
/// The table auto-sizes columns to fit the widest content (including
/// headers). Renders three separator lines: top (`┬`), middle (`┼`),
/// and bottom (`┴`).
#[derive(Debug, Clone)]
pub struct Table {
    /// Column definitions (header text + alignment).
    pub columns: Vec<Column>,
    /// Data rows with optional sparse cells.
    pub rows: Vec<Row>,
}

impl Table {
    /// Render the table to a list of lines (without trailing newlines).
    ///
    /// The output contains:
    /// 1. A top separator with `┬` at column joins
    /// 2. A header row with column names
    /// 3. A middle separator with `┼` at column joins
    /// 4. Data rows with `│` column separators
    /// 5. A bottom separator with `┴` at column joins
    pub fn render(&self) -> Vec<String> {
        let widths = self.compute_column_widths();
        let mut lines = Vec::new();

        lines.push(self.render_separator(&widths, '─', '┬'));
        lines.push(self.render_header(&widths));
        lines.push(self.render_separator(&widths, '─', '┼'));

        for row in &self.rows {
            lines.push(self.render_row(row, &widths));
        }

        lines.push(self.render_separator(&widths, '─', '┴'));
        lines
    }

    /// Compute the display width for each column.
    ///
    /// Width is the maximum of the header length and all cell content
    /// lengths in that column, plus 1 space of padding on each side.
    fn compute_column_widths(&self) -> Vec<usize> {
        self.columns
            .iter()
            .enumerate()
            .map(|(i, col)| {
                let header_width = col.header.chars().count();
                let max_cell = self
                    .rows
                    .iter()
                    .filter_map(|row| row.cells.get(i).and_then(|c| c.as_ref()))
                    .map(|s| s.chars().count())
                    .max()
                    .unwrap_or(0);
                header_width.max(max_cell)
            })
            .collect()
    }

    /// Render a separator line with the given fill and join characters.
    ///
    /// No outer border characters — the containing box provides those.
    fn render_separator(&self, widths: &[usize], fill: char, join: char) -> String {
        let mut line = String::new();
        for (i, &w) in widths.iter().enumerate() {
            if i > 0 {
                line.push(join);
            }
            // +2 for padding (1 space each side)
            for _ in 0..w + 2 {
                line.push(fill);
            }
        }
        line
    }

    /// Render the header row with column names.
    fn render_header(&self, widths: &[usize]) -> String {
        let cells: Vec<Option<String>> = self
            .columns
            .iter()
            .map(|col| Some(col.header.clone()))
            .collect();
        let dummy_row = Row { cells };
        self.render_row(&dummy_row, widths)
    }

    /// Render a single data row (no outer borders — the containing box provides those).
    fn render_row(&self, row: &Row, widths: &[usize]) -> String {
        let mut line = String::new();
        for (i, &w) in widths.iter().enumerate() {
            if i > 0 {
                line.push('│');
            }
            line.push(' ');

            let content = row
                .cells
                .get(i)
                .and_then(|c| c.as_ref())
                .map(|s| s.as_str())
                .unwrap_or("");
            let content_width = content.chars().count();
            let padding = w.saturating_sub(content_width);
            let align = self.columns.get(i).map(|c| c.align).unwrap_or(Align::Left);

            match align {
                Align::Left => {
                    line.push_str(content);
                    for _ in 0..padding {
                        line.push(' ');
                    }
                }
                Align::Right => {
                    for _ in 0..padding {
                        line.push(' ');
                    }
                    line.push_str(content);
                }
            }

            line.push(' ');
        }
        line
    }
}
