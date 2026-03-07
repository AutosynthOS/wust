//! Tree-style disassembly renderer with control flow visualization.
//!
//! Takes [`DisasmMetadata`] and produces a formatted string with:
//! - A function signature header line
//! - Byte offset prefixes for each instruction
//! - Box-drawing characters for forward conditional branch regions
//! - Right-aligned annotations
//!
//! The renderer is backend-agnostic — it works with any instruction width
//! and any instruction set.

use std::fmt::Write;

use super::{DisasmMetadata, RegisterRenames};

/// A forward conditional branch region, used for nesting visualization.
///
/// The region spans from the branch instruction to its target. Instructions
/// between `source` and `target` are drawn with an extra nesting level.
struct NestRegion {
    /// Byte offset of the branch instruction (region opens here).
    source: usize,
    /// Byte offset of the branch target (region closes here).
    target: usize,
}

/// Render disassembly metadata to a tree-style string.
///
/// This is the main entry point for the renderer. It:
/// 1. Applies register renames to instruction text
/// 2. Identifies forward conditional branches for nesting
/// 3. Computes alignment columns
/// 4. Walks instructions, emitting box-drawing characters
pub fn render_metadata(meta: &DisasmMetadata, renames: Option<&RegisterRenames>) -> String {
    if meta.instructions.is_empty() {
        return String::new();
    }

    let regions = collect_nest_regions(meta);
    let annotation_col = compute_annotation_column(meta, renames, &regions);

    let mut out = String::new();
    render_header(&mut out, meta);
    render_instructions(&mut out, meta, renames, &regions, annotation_col);
    out
}

/// Collect forward conditional branches as nesting regions.
fn collect_nest_regions(meta: &DisasmMetadata) -> Vec<NestRegion> {
    let mut regions: Vec<NestRegion> = meta
        .branches
        .iter()
        .filter(|b| b.is_conditional && b.target > b.offset)
        .map(|b| NestRegion {
            source: b.offset,
            target: b.target,
        })
        .collect();
    // Sort by source offset, then by target (wider regions first).
    regions.sort_by(|a, b| a.source.cmp(&b.source).then(b.target.cmp(&a.target)));
    regions
}

/// Compute the column where annotations should start.
///
/// This is based on the widest instruction line (offset + pipes + text)
/// plus a gutter of 2 spaces.
fn compute_annotation_column(
    meta: &DisasmMetadata,
    renames: Option<&RegisterRenames>,
    regions: &[NestRegion],
) -> usize {
    let mut max_width = 0usize;
    for inst in &meta.instructions {
        let text = apply_renames(&inst.text, renames);
        let is_branch_open = regions.iter().any(|r| r.source == inst.offset);
        let prefix_width = if is_branch_open {
            let depth = nesting_depth_before_open(inst.offset, regions);
            branch_open_prefix_width(depth)
        } else {
            let depth = nesting_depth(inst.offset, regions);
            pipe_prefix_width(depth)
        };
        // "XXXX " (5) + prefix + text
        let line_width = 5 + prefix_width + display_width(&text);
        max_width = max_width.max(line_width);
    }
    max_width + 2
}

/// Render the function signature header.
fn render_header(out: &mut String, meta: &DisasmMetadata) {
    if let Some(sig) = &meta.signature {
        writeln!(out, "     {sig}").unwrap();
    }
}

/// Render all instructions with control flow edges.
fn render_instructions(
    out: &mut String,
    meta: &DisasmMetadata,
    renames: Option<&RegisterRenames>,
    regions: &[NestRegion],
    annotation_col: usize,
) {
    for inst in &meta.instructions {
        let text = apply_renames(&inst.text, renames);
        let offset = inst.offset;

        // Check if this instruction is a branch-open point.
        let is_branch_open = regions.iter().any(|r| r.source == offset);
        // Check if this instruction is a branch-target point.
        let is_branch_target = regions.iter().any(|r| r.target == offset);

        if is_branch_target {
            emit_branch_target_label(out, offset, regions, meta, annotation_col);
        }

        if is_branch_open {
            let depth = nesting_depth_before_open(offset, regions);
            emit_branch_open_line(out, offset, &text, depth, &inst.annotation, annotation_col);
        } else {
            let depth = nesting_depth(offset, regions);
            emit_instruction_line(out, offset, &text, depth, &inst.annotation, annotation_col);
        }
    }
}

/// Emit the `╰─→ LX:` label line at a branch target.
fn emit_branch_target_label(
    out: &mut String,
    offset: usize,
    regions: &[NestRegion],
    meta: &DisasmMetadata,
    _annotation_col: usize,
) {
    let label_name = find_label_name(meta, offset);
    // The depth is for the region that just closed — one level above the target's depth.
    let depth_after = nesting_depth(offset, regions);
    let mut line = format!("     ");
    append_branch_target_prefix(&mut line, depth_after);
    write!(line, "{label_name}:").unwrap();
    writeln!(out, "{}", line.trim_end()).unwrap();
}

/// Find the display name for a label at a given byte offset.
fn find_label_name(meta: &DisasmMetadata, offset: usize) -> String {
    meta.block_labels
        .iter()
        .find(|l| l.offset == offset)
        .map(|l| {
            l.name
                .clone()
                .unwrap_or_else(|| format!("{}", l.id))
        })
        .unwrap_or_else(|| format!("@{offset:04x}"))
}

/// Emit a normal instruction line with pipe prefix.
fn emit_instruction_line(
    out: &mut String,
    offset: usize,
    text: &str,
    depth: usize,
    annotation: &Option<String>,
    annotation_col: usize,
) {
    let mut line = format!("{offset:04x} ");
    append_pipe_prefix(&mut line, depth);
    line.push_str(text);
    append_annotation(&mut line, annotation, annotation_col);
    writeln!(out, "{}", line.trim_end()).unwrap();
}

/// Emit a branch-open instruction line with `├─╮` connector.
fn emit_branch_open_line(
    out: &mut String,
    offset: usize,
    text: &str,
    depth: usize,
    annotation: &Option<String>,
    annotation_col: usize,
) {
    let mut line = format!("{offset:04x} ");
    append_branch_open_prefix(&mut line, depth);
    line.push_str(text);
    append_annotation(&mut line, annotation, annotation_col);
    writeln!(out, "{}", line.trim_end()).unwrap();
}

// ── Prefix builders ──────────────────────────────────────────────────

/// Build the pipe prefix: `│  ` at the outermost level, `│ ` for each
/// additional nesting level.
///
/// depth=0: `│  ` (3 chars)
/// depth=1: `│ │  ` (5 chars)
/// depth=2: `│ │ │  ` (7 chars)
fn append_pipe_prefix(out: &mut String, depth: usize) {
    out.push('│');
    for _ in 0..depth {
        out.push_str(" │");
    }
    out.push_str("  ");
}

/// Width of the pipe prefix for a given nesting depth.
fn pipe_prefix_width(depth: usize) -> usize {
    // '│' + depth * ' │' + '  '
    1 + depth * 2 + 2
}

/// Width of the branch-open prefix for a given nesting depth.
fn branch_open_prefix_width(depth: usize) -> usize {
    // depth * '│ ' + '├─╮ '
    depth * 2 + 4
}

/// Build the `├─╮ ` prefix for a branch-open line.
///
/// depth=0: `├─╮ ` (4 chars)
/// depth=1: `│ ├─╮ ` (6 chars)
fn append_branch_open_prefix(out: &mut String, depth: usize) {
    for _ in 0..depth {
        out.push_str("│ ");
    }
    out.push_str("├─╮ ");
}

/// Build the `╰─→ ` prefix for a branch-target label.
///
/// depth=0: `╰─→ ` (4 chars)
/// depth=1: `│ ╰─→ ` (6 chars — note: one outer region is still active)
fn append_branch_target_prefix(out: &mut String, depth: usize) {
    for _ in 0..depth {
        out.push_str("│ ");
    }
    out.push_str("╰─→ ");
}

// ── Annotation alignment ─────────────────────────────────────────────

/// Append a right-aligned annotation comment to a line.
fn append_annotation(line: &mut String, annotation: &Option<String>, annotation_col: usize) {
    if let Some(note) = annotation {
        if !note.is_empty() {
            pad_to(line, annotation_col);
            write!(line, "; {note}").unwrap();
        }
    }
}

/// Pad a string with spaces until it reaches the target column.
fn pad_to(s: &mut String, target_col: usize) {
    let current = display_width(s);
    for _ in current..target_col {
        s.push(' ');
    }
}

/// Compute the display width of a string (character count).
fn display_width(s: &str) -> usize {
    s.chars().count()
}

// ── Nesting depth computation ────────────────────────────────────────

/// Compute the nesting depth for an instruction at a given byte offset.
///
/// An instruction is nested inside a region if its offset is strictly
/// greater than the region's source and strictly less than the region's
/// target.
fn nesting_depth(offset: usize, regions: &[NestRegion]) -> usize {
    regions
        .iter()
        .filter(|r| offset > r.source && offset < r.target)
        .count()
}

/// Compute the nesting depth for a branch-open instruction.
///
/// The branch-open instruction itself is NOT inside its own region,
/// but it IS inside any regions that contain it.
fn nesting_depth_before_open(offset: usize, regions: &[NestRegion]) -> usize {
    regions
        .iter()
        .filter(|r| r.source != offset && offset > r.source && offset < r.target)
        .count()
}

// ── Register rename application ──────────────────────────────────────

/// Apply register renames to instruction text, or return it unchanged.
fn apply_renames(text: &str, renames: Option<&RegisterRenames>) -> String {
    match renames {
        Some(r) => r.apply(text),
        None => text.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::disasm::{BlockLabel, BranchInfo, DisasmInst, DisasmMetadata, RegisterRenames};
    use crate::ir::block::BlockId;

    /// Build a minimal metadata for testing: three instructions, one forward
    /// conditional branch from offset 4 to offset 12.
    fn simple_branch_metadata() -> DisasmMetadata {
        DisasmMetadata {
            instructions: vec![
                DisasmInst {
                    offset: 0,
                    text: "movz  w9, #0x1".into(),
                    annotation: Some("load constant".into()),
                },
                DisasmInst {
                    offset: 4,
                    text: "b.gt  L0".into(),
                    annotation: Some("if n > 1".into()),
                },
                DisasmInst {
                    offset: 8,
                    text: "ret   x30".into(),
                    annotation: Some("return n".into()),
                },
                DisasmInst {
                    offset: 12,
                    text: "add   w9, w9, w10".into(),
                    annotation: None,
                },
            ],
            block_labels: vec![BlockLabel {
                offset: 12,
                id: BlockId::User(0),
                name: Some("L0".into()),
            }],
            branches: vec![BranchInfo {
                offset: 4,
                target: 12,
                is_conditional: true,
            }],
            signature: Some("fn test<0>(w9<i32>) -> w9<i32>".into()),
        }
    }

    #[test]
    fn render_signature_header() {
        let meta = simple_branch_metadata();
        let output = meta.render(None);
        assert!(
            output.starts_with("     fn test<0>(w9<i32>) -> w9<i32>\n"),
            "output should start with signature header, got:\n{output}"
        );
    }

    #[test]
    fn render_branch_open_marker() {
        let meta = simple_branch_metadata();
        let output = meta.render(None);
        // The branch instruction at offset 4 should have ├─╮ connector.
        let branch_line = output.lines().find(|l| l.starts_with("0004")).unwrap();
        assert!(
            branch_line.contains("├─╮"),
            "branch line should have ├─╮ connector, got: {branch_line}"
        );
    }

    #[test]
    fn render_nested_instruction() {
        let meta = simple_branch_metadata();
        let output = meta.render(None);
        // The instruction at offset 8 (inside the branch region) should be nested.
        let nested_line = output.lines().find(|l| l.starts_with("0008")).unwrap();
        assert!(
            nested_line.contains("│ │"),
            "nested line should have │ │ prefix, got: {nested_line}"
        );
    }

    #[test]
    fn render_branch_target_label() {
        let meta = simple_branch_metadata();
        let output = meta.render(None);
        // The target label at offset 12 should have ╰─→ connector.
        let label_line = output
            .lines()
            .find(|l| l.contains("╰─→"))
            .expect("should have a branch target label line");
        assert!(
            label_line.contains("L0:"),
            "label line should contain L0:, got: {label_line}"
        );
    }

    #[test]
    fn render_annotations_aligned() {
        let meta = simple_branch_metadata();
        let output = meta.render(None);
        // All annotation lines should have ";" at the same column.
        let annotated: Vec<&str> = output.lines().filter(|l| l.contains(';')).collect();
        assert!(
            annotated.len() >= 2,
            "should have at least 2 annotated lines"
        );
        let cols: Vec<usize> = annotated
            .iter()
            .map(|l| l.chars().position(|c| c == ';').unwrap())
            .collect();
        let first = cols[0];
        for (i, &col) in cols.iter().enumerate() {
            assert_eq!(
                col, first,
                "annotation column mismatch: line {} at col {}, expected {}",
                i, col, first
            );
        }
    }

    #[test]
    fn render_with_register_renames() {
        let mut meta = DisasmMetadata::new();
        meta.instructions.push(DisasmInst {
            offset: 0,
            text: "ldr x9, [x29, #0]".into(),
            annotation: None,
        });

        let mut renames = RegisterRenames::new();
        renames.add("x29", "g.lb");

        let output = meta.render(Some(&renames));
        assert!(
            output.contains("g.lb"),
            "output should contain renamed register, got:\n{output}"
        );
        assert!(
            !output.contains("x29"),
            "output should not contain original register name, got:\n{output}"
        );
    }

    #[test]
    fn render_empty_metadata() {
        let meta = DisasmMetadata::new();
        let output = meta.render(None);
        assert!(output.is_empty(), "empty metadata should produce empty output");
    }

    #[test]
    fn render_no_branches() {
        let meta = DisasmMetadata {
            instructions: vec![
                DisasmInst {
                    offset: 0,
                    text: "movz  w9, #0x1".into(),
                    annotation: Some("const".into()),
                },
                DisasmInst {
                    offset: 4,
                    text: "ret   x30".into(),
                    annotation: None,
                },
            ],
            block_labels: Vec::new(),
            branches: Vec::new(),
            signature: None,
        };
        let output = meta.render(None);
        // Both lines should have simple │ prefix with no nesting.
        for line in output.lines() {
            if line.starts_with("0") {
                assert!(
                    line.contains("│  "),
                    "simple lines should have │  prefix, got: {line}"
                );
            }
        }
    }

    #[test]
    fn nesting_depth_computation() {
        let regions = vec![
            NestRegion {
                source: 4,
                target: 20,
            },
            NestRegion {
                source: 8,
                target: 16,
            },
        ];

        assert_eq!(nesting_depth(0, &regions), 0, "before any region");
        assert_eq!(nesting_depth(6, &regions), 1, "inside outer only");
        assert_eq!(nesting_depth(12, &regions), 2, "inside both");
        assert_eq!(nesting_depth(18, &regions), 1, "inside outer only, past inner");
        assert_eq!(nesting_depth(24, &regions), 0, "after all regions");
    }

    #[test]
    fn blockid_display_in_label() {
        let meta = DisasmMetadata {
            instructions: vec![
                DisasmInst {
                    offset: 0,
                    text: "b.gt L3".into(),
                    annotation: None,
                },
                DisasmInst {
                    offset: 4,
                    text: "nop".into(),
                    annotation: None,
                },
                DisasmInst {
                    offset: 8,
                    text: "nop".into(),
                    annotation: None,
                },
            ],
            block_labels: vec![BlockLabel {
                offset: 8,
                id: BlockId::User(3),
                name: None,
            }],
            branches: vec![BranchInfo {
                offset: 0,
                target: 8,
                is_conditional: true,
            }],
            signature: None,
        };
        let output = meta.render(None);
        // Should use BlockId's Display impl for the label.
        assert!(
            output.contains("L3:"),
            "should use BlockId Display for User(3), got:\n{output}"
        );
    }
}
