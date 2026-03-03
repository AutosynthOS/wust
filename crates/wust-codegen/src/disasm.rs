use std::fmt::Write;

/// A block of machine code — function body, shared handler, trampoline, etc.
///
/// All blocks are rendered the same way: pipe-style with optional IR
/// annotations. The only difference between a "function" and a "raw section"
/// is whether `annotations` is present.
pub struct Block {
    /// Display name — includes signature for functions
    /// (e.g. "fn fib<0>(x9: i32) -> x9: i32").
    pub name: String,
    /// Raw u32 instruction words.
    pub code: Vec<u32>,
    /// Byte offset of this block's first word in the full code buffer.
    /// Used for absolute branch target resolution.
    pub base_offset: usize,
    /// Optional IR annotations. When present, enables the tree-style
    /// renderer with nested control flow, fuel checks, and source-op labels.
    pub annotations: Option<BlockAnnotations>,
}

/// IR-level metadata that enables annotated rendering of a function block.
pub struct BlockAnnotations {
    /// Word-offset markers: prologue, each IR instruction, yield, completion.
    pub markers: Vec<usize>,
    /// Number of IR instructions (for mapping markers to regions).
    pub ir_inst_count: usize,
    /// For each IR instruction, the index of the source parsed wasm op.
    pub source_ops: Vec<u32>,
    /// Human-readable label for each parsed wasm op.
    pub op_labels: Vec<String>,
    /// Label index → word offset relative to this block's code start.
    pub label_offsets: Vec<Option<usize>>,
}

/// Output of the codegen pipeline for a module.
pub struct CodegenOutput {
    /// All code blocks in emission order.
    pub blocks: Vec<Block>,
    /// Global label map: absolute byte offset → label name.
    pub labels: Vec<(usize, String)>,
}

impl CodegenOutput {
    /// Render all blocks in pipe-style visualization.
    ///
    /// Annotated blocks get the tree-style renderer with nested control
    /// flow and IR comments. Unannotated blocks get flat disassembly.
    /// Branch targets are resolved through the global label map.
    pub fn render(&self) -> String {
        let mut out = String::new();
        for block in &self.blocks {
            render_block(&mut out, block, &self.labels);
            writeln!(out).unwrap();
        }
        out
    }
}

// ============================================================
// Unified block renderer
// ============================================================

/// Render a single block — dispatches to annotated or flat rendering.
fn render_block(out: &mut String, block: &Block, labels: &[(usize, String)]) {
    if block.code.is_empty() {
        return;
    }

    writeln!(out, "     fn {}", block.name).unwrap();

    match &block.annotations {
        Some(ann) => render_annotated(out, block, ann, labels),
        None => render_flat(out, block, labels),
    }

    // ir_col doesn't matter for the closing line — use a large value.
    emit_header(out, 0, "end", "╰─", None, 999);
}

/// Flat rendering for unannotated blocks (handlers, trampolines, etc).
fn render_flat(out: &mut String, block: &Block, labels: &[(usize, String)]) {
    for (i, &word) in block.code.iter().enumerate() {
        let byte_off = block.base_offset + i * 4;
        let asm = resolve_asm(word, byte_off, labels);
        emit_line(out, byte_off, &asm, 0, None, 999);
    }
}

/// Annotated tree-style rendering for function blocks.
fn render_annotated(
    out: &mut String,
    block: &Block,
    ann: &BlockAnnotations,
    labels: &[(usize, String)],
) {
    let ctx = TreeCtx::build(block, ann, labels);
    render_tree(out, &ctx, 0, ctx.regions.len(), 0);
}

// ============================================================
// Instruction decoding and branch resolution
// ============================================================

/// Decode and normalize an instruction, resolving branch targets via labels.
fn resolve_asm(word: u32, byte_off: usize, labels: &[(usize, String)]) -> String {
    let asm = normalize_asm(&decode_instruction(word));
    if let Some(offset) = branch_word_offset(word) {
        let word_idx = byte_off / 4;
        let target_byte = ((word_idx as i64 + offset as i64) * 4) as usize;
        if let Some((_, name)) = labels.iter().find(|(off, _)| *off == target_byte) {
            return rewrite_branch_target(&asm, name);
        }
        return rewrite_branch_target(&asm, &format!("@{target_byte:04x}"));
    }
    asm
}

/// Decode a single instruction word using disarm64.
fn decode_instruction(word: u32) -> String {
    match disarm64::decoder::decode(word) {
        Some(insn) => format!("{insn}"),
        None => format!(".word 0x{word:08x}"),
    }
}

/// Extract the signed word offset from a branch instruction, or None if
/// the instruction is not a branch.
fn branch_word_offset(word: u32) -> Option<i32> {
    let top8 = word >> 24;
    match top8 {
        // B (unconditional): 0x14..0x17
        0x14..=0x17 => {
            let imm26 = (word & 0x03FF_FFFF) as i32;
            Some(sign_extend(imm26, 26))
        }
        // BL: 0x94..0x97
        0x94..=0x97 => {
            let imm26 = (word & 0x03FF_FFFF) as i32;
            Some(sign_extend(imm26, 26))
        }
        // B.cond: 0x54
        0x54 => {
            let imm19 = ((word >> 5) & 0x7FFFF) as i32;
            Some(sign_extend(imm19, 19))
        }
        // CBZ/CBNZ (32-bit): 0x34, 0x35
        // CBZ/CBNZ (64-bit): 0xB4, 0xB5
        0x34 | 0x35 | 0xB4 | 0xB5 => {
            let imm19 = ((word >> 5) & 0x7FFFF) as i32;
            Some(sign_extend(imm19, 19))
        }
        _ => None,
    }
}

fn sign_extend(val: i32, bits: u32) -> i32 {
    let shift = 32 - bits;
    (val << shift) >> shift
}

// ============================================================
// Tree-style rendering (annotated blocks)
// ============================================================

/// A non-empty region of machine code corresponding to one IR region.
struct Region {
    start: usize,
    end: usize,
    /// Original marker index. ir_idx = marker_idx - 1 for non-prologue.
    marker_idx: usize,
}

/// Precomputed context for tree-style rendering.
struct TreeCtx<'a> {
    block: &'a Block,
    labels: &'a [(usize, String)],
    regions: Vec<Region>,
    /// (source_ri, target_ri) for each forward conditional branch.
    branches: Vec<(usize, usize)>,
    /// Per-function label map: word offset → label name (L0, L1, ...).
    local_labels: Vec<Option<String>>,
    /// word_idx → annotation string (source op label).
    ir_at: Vec<Option<String>>,
    /// Column where IR annotations start.
    ir_col: usize,
}

impl<'a> TreeCtx<'a> {
    fn build(block: &'a Block, ann: &'a BlockAnnotations, labels: &'a [(usize, String)]) -> Self {
        let total_words = block.code.len();
        let max_regions = ann.ir_inst_count + 1;
        let regions = collect_regions(&ann.markers, total_words, max_regions);

        let local_labels = build_local_label_map(&ann.label_offsets, total_words);
        let branches = find_forward_branches(&regions, &block.code);
        let ir_at = build_source_op_annotations(ann, &regions, total_words);

        let max_branch_depth = (0..regions.len())
            .map(|ri| {
                branches
                    .iter()
                    .filter(|&&(src, tgt)| ri > src && ri < tgt)
                    .count()
            })
            .max()
            .unwrap_or(0);
        let max_depth = max_branch_depth + 1;

        let asm_width = compute_asm_width(&block.code, &regions);
        let ir_col = 9 + 2 * max_depth + asm_width + 4;

        Self {
            block,
            labels,
            regions,
            branches,
            local_labels,
            ir_at,
            ir_col,
        }
    }
}

/// Recursively render regions[ri_start..ri_end] at the given nesting depth.
fn render_tree(
    out: &mut String,
    ctx: &TreeCtx,
    ri_start: usize,
    ri_end: usize,
    depth: usize,
) {
    let mut ri = ri_start;
    while ri < ri_end {
        // Check if a conditional branch starts at this region.
        if let Some(&(_, target)) = ctx.branches.iter().find(|&&(src, _)| src == ri) {
            let region = &ctx.regions[ri];

            // Render instructions before the branch (all except last word).
            if region.end > region.start + 1 {
                render_words(out, ctx, region.start, region.end - 1, depth);
            }

            // Show the branch instruction with ├─╮ connector.
            let branch_word_idx = region.end - 1;
            let branch_word = ctx.block.code[branch_word_idx];
            let raw_asm = normalize_asm(&decode_instruction(branch_word));

            // Resolve branch target label within the target region.
            let target_region = &ctx.regions[target];
            let target_label = (target_region.start..target_region.end)
                .find_map(|w| ctx.local_labels.get(w).and_then(|l| l.as_deref()))
                .unwrap_or("?");
            let asm = rewrite_branch_target(&raw_asm, target_label);
            let ir_note = ctx.ir_at.get(branch_word_idx).and_then(|n| n.as_deref());

            emit_branch_open(out, branch_word_idx * 4, &asm, depth, ir_note, ctx.ir_col);

            // Render fall-through body at depth+1.
            render_tree(out, ctx, ri + 1, target, depth + 1);
            emit_header(out, depth + 1, "end", "╰─", None, ctx.ir_col);

            ri = target;
            continue;
        }

        // No branch — render region's instructions normally.
        render_words(out, ctx, ctx.regions[ri].start, ctx.regions[ri].end, depth);
        ri += 1;
    }
}

/// Render machine code words[start..end], detecting fuel checks.
fn render_words(out: &mut String, ctx: &TreeCtx, start: usize, end: usize, depth: usize) {
    let mut wi = start;
    while wi < end {
        let word = ctx.block.code[wi];

        // Fuel check: subs x21, x21, #N followed by b.le
        if wi + 1 < end && is_fuel_subs(word) && is_b_le(ctx.block.code[wi + 1]) {
            let asm = normalize_asm(&decode_instruction(word));
            let ir = ctx.ir_at.get(wi).and_then(|n| n.as_deref());
            emit_line(out, wi * 4, &asm, depth, ir, ctx.ir_col);

            let b_le = ctx.block.code[wi + 1];
            let raw_b_le = normalize_asm(&decode_instruction(b_le));
            let b_le_asm = rewrite_branch_target(&raw_b_le, "suspend");
            emit_branch_open(out, (wi + 1) * 4, &b_le_asm, depth, None, ctx.ir_col);

            // Render the single-instruction cold stub (brk) inline.
            let cold_off = branch_word_offset(b_le).unwrap();
            let cold_start = ((wi + 1) as i64 + cold_off as i64) as usize;
            let cold_word = ctx.block.code[cold_start];
            let cold_byte_off = ctx.block.base_offset + cold_start * 4;
            let cold_asm = resolve_asm(cold_word, cold_byte_off, ctx.labels);
            emit_block_end_line(out, cold_start * 4, &cold_asm, depth + 1, Some("suspend"), ctx.ir_col);

            wi += 2;
            continue;
        }

        // Normal instruction — resolve via global labels.
        let byte_off = ctx.block.base_offset + wi * 4;
        let asm = resolve_asm(word, byte_off, ctx.labels);
        let ir = ctx.ir_at.get(wi).and_then(|n| n.as_deref());
        emit_line(out, wi * 4, &asm, depth, ir, ctx.ir_col);
        wi += 1;
    }
}


// ============================================================
// Line rendering helpers
// ============================================================

fn pipe_prefix(depth: usize) -> String {
    let mut s = String::with_capacity(2 * (depth + 1) + 1);
    for i in 0..=depth {
        s.push('│');
        if i < depth { s.push(' '); } else { s.push_str("  "); }
    }
    s
}

fn header_prefix(depth: usize, connector: &str) -> String {
    let mut s = String::with_capacity(2 * depth + 3);
    for _ in 0..depth { s.push_str("│ "); }
    s.push_str(connector);
    s.push(' ');
    s
}

fn branch_open_prefix(depth: usize) -> String {
    let mut s = String::with_capacity(2 * depth + 4);
    for _ in 0..depth { s.push_str("│ "); }
    s.push_str("├─╮ ");
    s
}


fn emit_line(out: &mut String, byte_off: usize, asm: &str, depth: usize, ir: Option<&str>, ir_col: usize) {
    let mut line = format!("{byte_off:04x} {}{asm}", pipe_prefix(depth));
    if let Some(note) = ir {
        if !note.is_empty() {
            pad_to(&mut line, ir_col, ' ');
            line.push_str(note);
        }
    }
    writeln!(out, "{}", line.trim_end()).unwrap();
}

fn emit_header(out: &mut String, depth: usize, label: &str, connector: &str, ir: Option<&str>, ir_col: usize) {
    let mut line = format!("     {}{label}", header_prefix(depth, connector));
    if let Some(note) = ir {
        if !note.is_empty() {
            pad_to(&mut line, ir_col, ' ');
            line.push_str(note);
        }
    }
    writeln!(out, "{}", line.trim_end()).unwrap();
}


fn emit_branch_open(out: &mut String, byte_off: usize, asm: &str, depth: usize, ir: Option<&str>, ir_col: usize) {
    let mut line = format!("{byte_off:04x} {}{asm}", branch_open_prefix(depth));
    if let Some(note) = ir {
        if !note.is_empty() {
            pad_to(&mut line, ir_col, ' ');
            line.push_str(note);
        }
    }
    writeln!(out, "{}", line.trim_end()).unwrap();
}

fn emit_block_end_line(out: &mut String, byte_off: usize, asm: &str, depth: usize, ir: Option<&str>, ir_col: usize) {
    let mut prefix = String::new();
    for _ in 0..depth { prefix.push_str("│ "); }
    prefix.push_str("╰─ ");

    let mut line = format!("{byte_off:04x} {prefix}{asm}");
    if let Some(note) = ir {
        if !note.is_empty() {
            pad_to(&mut line, ir_col, ' ');
            line.push_str(note);
        }
    }
    writeln!(out, "{}", line.trim_end()).unwrap();
}

// ============================================================
// String helpers
// ============================================================

/// Rewrite a branch instruction's hex target with a human-readable name.
fn rewrite_branch_target(asm: &str, label: &str) -> String {
    if let Some(pos) = asm.rfind("0x") {
        let start = if pos > 0 && asm.as_bytes()[pos - 1] == b'-' { pos - 1 } else { pos };
        let rest = &asm[pos + 2..];
        let hex_len = rest.find(|c: char| !c.is_ascii_hexdigit()).unwrap_or(rest.len());
        let end = pos + 2 + hex_len;
        format!("{}{label}{}", &asm[..start], &asm[end..])
    } else {
        asm.to_string()
    }
}

/// Expand tabs and rename global registers.
fn normalize_asm(s: &str) -> String {
    let normalized = if let Some(tab_pos) = s.find('\t') {
        let mnemonic = &s[..tab_pos];
        let rest = s[tab_pos..].trim_start_matches('\t');
        format!("{mnemonic:<6}{rest}")
    } else {
        s.to_string()
    };
    rename_registers(&normalized)
}

/// Rename global/special registers to readable names.
fn rename_registers(s: &str) -> String {
    let mut result = s.to_string();
    result = replace_at_word_boundary(&result, "x21", "g.fuel");
    result = replace_at_word_boundary(&result, "x29", "g.fp");
    result = replace_at_word_boundary(&result, "x20", "g.ctx");
    result = replace_at_word_boundary(&result, "x30", "g.lr");
    result = replace_at_word_boundary(&result, "sp", "g.sp");
    result
}

fn replace_at_word_boundary(s: &str, from: &str, to: &str) -> String {
    let bytes = s.as_bytes();
    let from_len = from.len();
    let mut result = String::with_capacity(s.len());
    let mut i = 0;
    while i < bytes.len() {
        if i + from_len <= bytes.len() && &s[i..i + from_len] == from {
            let left_ok = i == 0 || !bytes[i - 1].is_ascii_alphanumeric();
            let right_ok = i + from_len == bytes.len() || !bytes[i + from_len].is_ascii_alphanumeric();
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

fn display_width(s: &str) -> usize { s.chars().count() }

fn pad_to(s: &mut String, target_col: usize, fill: char) {
    let current = display_width(s);
    for _ in current..target_col { s.push(fill); }
}


// ============================================================
// Data collection helpers
// ============================================================

/// Build per-function label map: word offset → "L0", "L1", etc.
fn build_local_label_map(label_offsets: &[Option<usize>], total_words: usize) -> Vec<Option<String>> {
    let mut map: Vec<Option<String>> = vec![None; total_words + 1];
    for (label_idx, offset) in label_offsets.iter().enumerate() {
        if let Some(word_offset) = offset {
            if *word_offset < map.len() {
                map[*word_offset] = Some(format!("L{label_idx}"));
            }
        }
    }
    map
}

/// Build word_idx → annotation map from source op labels.
fn build_source_op_annotations(
    ann: &BlockAnnotations,
    regions: &[Region],
    total_words: usize,
) -> Vec<Option<String>> {
    let mut annotations: Vec<Option<String>> = vec![None; total_words];

    if let Some(region) = regions.first() {
        if region.start < annotations.len() {
            annotations[region.start] = Some("prologue".into());
        }
    }

    let body_regions: Vec<&Region> = regions.iter().filter(|r| r.marker_idx > 0).collect();

    let mut i = 0;
    while i < body_regions.len() {
        let ir_idx = body_regions[i].marker_idx - 1;
        if ir_idx >= ann.source_ops.len() {
            i += 1;
            continue;
        }
        let source_op = ann.source_ops[ir_idx];

        let mut group_end = i + 1;
        while group_end < body_regions.len() {
            let idx = body_regions[group_end].marker_idx - 1;
            if idx >= ann.source_ops.len() || ann.source_ops[idx] != source_op {
                break;
            }
            group_end += 1;
        }

        let label = ann.op_labels.get(source_op as usize).map(|s| s.as_str()).unwrap_or("");
        if !label.is_empty() {
            let best = group_end - 1;
            let word = body_regions[best].start;
            if word < annotations.len() {
                annotations[word] = Some(label.to_string());
            }
        }

        i = group_end;
    }

    annotations
}

/// Collect non-empty regions from markers.
fn collect_regions(markers: &[usize], total_words: usize, max_regions: usize) -> Vec<Region> {
    let count = markers.len().min(max_regions);
    let mut regions = Vec::new();
    for region_idx in 0..count {
        let start = markers[region_idx];
        let end = if region_idx + 1 < markers.len() { markers[region_idx + 1] } else { total_words };
        if start == end { continue; }
        regions.push(Region { start, end, marker_idx: region_idx });
    }
    regions
}

/// Find all forward conditional branches as (source_ri, target_ri) pairs.
fn find_forward_branches(regions: &[Region], code: &[u32]) -> Vec<(usize, usize)> {
    let mut branches = Vec::new();
    for (ri, region) in regions.iter().enumerate() {
        if region.end == region.start { continue; }
        let last_word = code[region.end - 1];
        if !is_conditional_branch(last_word) { continue; }
        let offset = match branch_word_offset(last_word) {
            Some(o) => o,
            None => continue,
        };
        let target_word = (region.end as i64 - 1 + offset as i64) as usize;
        if let Some(target_ri) = regions.iter().position(|r| r.start <= target_word && target_word < r.end) {
            if target_ri > ri {
                branches.push((ri, target_ri));
            }
        }
    }
    branches
}

/// Compute the display width of the longest normalized instruction.
fn compute_asm_width(code: &[u32], regions: &[Region]) -> usize {
    let mut max_w = 0usize;
    for region in regions {
        for word_idx in region.start..region.end {
            let asm = normalize_asm(&decode_instruction(code[word_idx]));
            max_w = max_w.max(display_width(&asm));
        }
    }
    let body_end = regions.last().map(|r| r.end).unwrap_or(0);
    for wi in body_end..code.len() {
        let asm = normalize_asm(&decode_instruction(code[wi]));
        max_w = max_w.max(display_width(&asm));
    }
    max_w + 2
}

// ============================================================
// Instruction classification helpers
// ============================================================

fn is_conditional_branch(word: u32) -> bool {
    let top8 = word >> 24;
    matches!(top8, 0x54 | 0x34 | 0x35 | 0xB4 | 0xB5)
}

fn is_fuel_subs(word: u32) -> bool {
    (word & 0xFFC0_03FF) == 0xF100_02B5
}

fn is_b_le(word: u32) -> bool {
    (word & 0xFF00_001F) == 0x5400_000D
}
