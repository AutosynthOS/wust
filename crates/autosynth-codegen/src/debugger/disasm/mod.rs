//! Backend-agnostic disassembly metadata and rendering.
//!
//! The lowerer populates [`DisasmMetadata`] during code generation. The
//! consumer can then add annotations, apply register renames, and call
//! [`DisasmMetadata::render`] to produce a tree-style visualization with
//! control flow edges drawn using box-drawing characters.
//!
//! # Example
//!
//! ```ignore
//! let (bytes, mut meta) = backend.lower_with_disasm(&func);
//! meta.instructions[3].annotation = Some("; local.get 0".into());
//! let output = meta.render(Some(&renames));
//! println!("{output}");
//! ```

/// Box-drawing renderers for function and block visualizations.
pub mod boxes;
mod render;
/// Column-aligned table renderer with sparse cells.
pub mod table;

use autosynth_ir::BlockId;

/// Metadata collected during lowering for disassembly rendering.
///
/// This is backend-agnostic — it stores text strings, byte offsets, and
/// branch relationships. The renderer uses this to draw control flow edges
/// without knowing the instruction set.
pub struct DisasmMetadata {
    /// Per-instruction disassembly entries (one per machine instruction).
    pub instructions: Vec<DisasmInst>,
    /// Block labels placed at specific byte offsets.
    pub block_labels: Vec<BlockLabel>,
    /// Branch instructions with their targets, used for control flow edges.
    pub branches: Vec<BranchInfo>,
    /// Function signature for the header line (e.g. "fn fib<0>(w9<i32>) -> w9<i32>").
    pub signature: Option<String>,
}

impl DisasmMetadata {
    /// Create empty metadata with no instructions.
    pub fn new() -> Self {
        Self {
            instructions: Vec::new(),
            block_labels: Vec::new(),
            branches: Vec::new(),
            signature: None,
        }
    }

    /// Render the metadata to a tree-style disassembly string.
    ///
    /// If `renames` is provided, register names in instruction text are
    /// rewritten according to the rename map before rendering.
    pub fn render(&self, renames: Option<&RegisterRenames>) -> String {
        render::render_metadata(self, renames)
    }
}

/// A single disassembled machine instruction.
pub struct DisasmInst {
    /// Byte offset from the start of the function.
    pub offset: usize,
    /// Formatted instruction text (e.g. "add  x9, x10, x11").
    pub text: String,
    /// Optional right-aligned comment (e.g. "; prologue").
    pub annotation: Option<String>,
}

/// A label placed at a byte offset, marking the start of a block.
pub struct BlockLabel {
    /// Byte offset where this label appears.
    pub offset: usize,
    /// The IR block this label corresponds to.
    pub id: BlockId,
    /// Optional custom display name. If None, the BlockId's Display is used.
    pub name: Option<String>,
}

/// A branch instruction and its target, used for drawing control flow edges.
pub struct BranchInfo {
    /// Byte offset of the branch instruction.
    pub offset: usize,
    /// Byte offset of the branch target.
    pub target: usize,
    /// Whether this is a conditional branch (draws nested regions) or
    /// unconditional (draws a simple arrow).
    pub is_conditional: bool,
}

/// Maps physical register names to logical display names.
///
/// Applied to instruction text before rendering. Replacement is done at
/// word boundaries to avoid partial matches (e.g. "x20" inside "x200"
/// is not replaced).
///
/// # Example
///
/// ```
/// use autosynth_codegen::disasm::RegisterRenames;
///
/// let mut renames = RegisterRenames::new();
/// renames.add("x29", "g.lb");
/// renames.add("x20", "g.ctx");
/// assert_eq!(renames.apply("ldr x9, [x29, #0]"), "ldr x9, [g.lb, #0]");
/// ```
pub struct RegisterRenames {
    /// Ordered list of (from, to) pairs. Longer names are matched first
    /// to prevent partial replacement (e.g. "x20" before "x2").
    renames: Vec<(String, String)>,
}

impl RegisterRenames {
    /// Create an empty rename map.
    pub fn new() -> Self {
        Self {
            renames: Vec::new(),
        }
    }

    /// Add a register rename. Order of insertion matters — add longer
    /// register names first if they share a prefix (e.g. "x20" before "x2").
    pub fn add(&mut self, from: &str, to: &str) {
        self.renames.push((from.to_string(), to.to_string()));
        // Sort by descending length to prevent partial matches.
        self.renames.sort_by(|a, b| b.0.len().cmp(&a.0.len()));
    }

    /// Apply all renames to a string, replacing at word boundaries.
    pub fn apply(&self, text: &str) -> String {
        let mut result = text.to_string();
        for (from, to) in &self.renames {
            result = replace_at_word_boundary(&result, from, to);
        }
        result
    }
}

/// Replace `from` with `to` in `s`, but only at word boundaries.
///
/// A word boundary means the character before the match (if any) is not
/// alphanumeric, and the character after the match (if any) is not
/// alphanumeric. This prevents replacing "x2" inside "x20".
fn replace_at_word_boundary(s: &str, from: &str, to: &str) -> String {
    let bytes = s.as_bytes();
    let from_len = from.len();
    let mut result = String::with_capacity(s.len());
    let mut i = 0;
    while i < bytes.len() {
        if i + from_len <= bytes.len() && &s[i..i + from_len] == from {
            let left_ok = i == 0 || !bytes[i - 1].is_ascii_alphanumeric();
            let right_ok =
                i + from_len == bytes.len() || !bytes[i + from_len].is_ascii_alphanumeric();
            if left_ok && right_ok {
                result.push_str(to);
                i += from_len;
                continue;
            }
        }
        result.push(bytes[i] as char);
        i += 1;
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn word_boundary_replacement() {
        assert_eq!(replace_at_word_boundary("x29", "x29", "g.lb"), "g.lb");
        assert_eq!(
            replace_at_word_boundary("ldr x9, [x29, #0]", "x29", "g.lb"),
            "ldr x9, [g.lb, #0]"
        );
        // Should not replace x2 inside x29.
        assert_eq!(replace_at_word_boundary("x29", "x2", "BAD"), "x29");
    }
}
