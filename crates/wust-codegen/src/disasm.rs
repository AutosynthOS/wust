use std::fmt::Write;

/// Output of the codegen pipeline for a single function.
pub struct FunctionOutput {
    /// The IR text (always available).
    pub ir: String,
    /// Raw u32 instruction words.
    pub code: Vec<u32>,
    /// Word-offset markers: prologue, each IR instruction, yield, completion.
    pub markers: Vec<usize>,
    /// Number of IR instructions (for mapping markers to regions).
    pub ir_inst_count: usize,
    /// For each IR instruction, the index of the source parsed wasm op.
    /// Same length as `ir_inst_count`.
    pub source_ops: Vec<u32>,
    /// Human-readable label for each parsed wasm op (indexed by source
    /// op index). Superinstructions show as expressions like
    /// `sub(local.get 0, 1)`.
    pub op_labels: Vec<String>,
    /// Ground-truth label offsets from the lowerer: label index → word
    /// offset relative to the function's code start. Used for branch
    /// target resolution instead of reconstructing from markers.
    pub label_offsets: Vec<Option<usize>>,
    /// Number of function parameters.
    pub param_count: usize,
    /// Number of function results.
    pub result_count: usize,
}

/// Output of the codegen pipeline for a module.
pub struct CodegenOutput {
    pub functions: Vec<(String, FunctionOutput)>,
}

impl CodegenOutput {
    /// Render an annotated inspection view.
    ///
    /// Each IR instruction is shown as a comment, followed by the asm
    /// instructions it produced, decoded via `disarm64`.
    pub fn render_inspect(&self) -> String {
        let mut out = String::new();

        for (name, func) in &self.functions {
            writeln!(out, ";;; func {name}").unwrap();
            writeln!(out).unwrap();
            render_function(&mut out, func);
            writeln!(out).unwrap();
        }

        out
    }

    /// Render a pipe-style block visualization.
    ///
    /// Shows control flow structure with box-drawing characters, branch
    /// arrows connecting blocks, address gutters, and IR annotations.
    pub fn render_blocks(&self) -> String {
        let mut out = String::new();

        for (name, func) in &self.functions {
            render_blocks_function(&mut out, name, func);
            writeln!(out).unwrap();
        }

        out
    }
}

/// Render a single function's annotated disassembly.
fn render_function(out: &mut String, func: &FunctionOutput) {
    let markers = &func.markers;
    let total_words = func.code.len();
    let ir_lines: Vec<&str> = func.ir.lines().collect();

    // Build a map from word offset → label name for branch target resolution.
    let label_at = build_label_map(&func.label_offsets, total_words);

    for region_idx in 0..markers.len() {
        let start = markers[region_idx];
        let end = if region_idx + 1 < markers.len() {
            markers[region_idx + 1]
        } else {
            total_words
        };

        if start == end {
            continue;
        }

        let label = region_label(region_idx, func.ir_inst_count, &ir_lines);

        // If this IR line is a DefLabel, emit it as a label header.
        if label.ends_with(':') {
            writeln!(out, "  {label}").unwrap();
        } else {
            writeln!(out, "  ;; {label}").unwrap();
        }

        for word_idx in start..end {
            let word = func.code[word_idx];
            let byte_off = word_idx * 4;
            let mnemonic = decode_instruction(word);

            // Try to resolve branch targets to labels.
            let annotation = resolve_branch_target(word, word_idx, &label_at);
            if let Some(target) = annotation {
                writeln!(out, "    {byte_off:04x}: {word:08x}  {mnemonic:<30} ; -> {target}")
                    .unwrap();
            } else {
                writeln!(out, "    {byte_off:04x}: {word:08x}  {mnemonic}").unwrap();
            }
        }
        writeln!(out).unwrap();
    }
}

/// Decode a single instruction word using disarm64.
fn decode_instruction(word: u32) -> String {
    match disarm64::decoder::decode(word) {
        Some(insn) => format!("{insn}"),
        None => format!(".word 0x{word:08x}"),
    }
}

/// Build a map from word offset → label string (e.g. "L0") for all
/// labels. Uses the ground-truth `label_offsets` from the lowerer.
fn build_label_map(
    label_offsets: &[Option<usize>],
    total_words: usize,
) -> Vec<Option<String>> {
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

/// If the instruction is a branch, compute its target word offset and look
/// up whether a label exists there.
fn resolve_branch_target(word: u32, source_word_idx: usize, label_at: &[Option<String>]) -> Option<&str> {
    let word_offset = branch_word_offset(word)?;
    let target = (source_word_idx as i64 + word_offset as i64) as usize;
    label_at.get(target)?.as_deref()
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

/// Determine the label for a region based on its index.
///
/// Layout: [prologue] [IR inst 0] [IR inst 1] ... [IR inst N-1] [yield] [completion]
fn region_label<'a>(region_idx: usize, ir_inst_count: usize, ir_lines: &[&'a str]) -> &'a str {
    if region_idx == 0 {
        return "prologue";
    }

    let ir_idx = region_idx - 1;
    if ir_idx < ir_inst_count {
        let line_idx = ir_idx + 1;
        if line_idx < ir_lines.len() {
            return ir_lines[line_idx].trim();
        }
        return "???";
    }

    let tail_idx = ir_idx - ir_inst_count;
    match tail_idx {
        0 => "yield handler",
        1 => "completion handler",
        _ => "???",
    }
}

// ============================================================
// Tree-style rendering
// ============================================================

/// A non-empty region of machine code corresponding to one IR region.
struct Region {
    start: usize,
    end: usize,
    /// Original marker index this region came from. Used to map back
    /// to IR instruction indices (ir_idx = marker_idx - 1 for
    /// non-prologue regions).
    marker_idx: usize,
}

/// Precomputed context for tree-style rendering.
struct TreeCtx<'a> {
    func: &'a FunctionOutput,
    /// Function name (for resolving self-calls).
    func_name: &'a str,
    regions: Vec<Region>,
    /// (source_ri, target_ri) for each forward conditional branch.
    branches: Vec<(usize, usize)>,
    label_at: Vec<Option<String>>,
    /// word_idx → annotation string. Set on the first word of each
    /// source-op group (so consecutive words from the same parsed wasm
    /// op only show the label once).
    ir_at: Vec<Option<String>>,
    /// Absolute column where IR annotations start.
    ir_col: usize,
}

impl<'a> TreeCtx<'a> {
    fn build(func: &'a FunctionOutput, func_name: &'a str) -> Self {
        let total_words = func.code.len();
        let max_regions = func.ir_inst_count + 1;
        let regions = collect_regions(
            &func.markers,
            total_words,
            max_regions,
        );

        let label_at = build_label_map(&func.label_offsets, total_words);
        let branches = find_forward_branches(&regions, &func.code);

        let ir_at = build_source_op_annotations(func, &regions);

        // Compute max nesting depth for IR column placement.
        let max_branch_depth = (0..regions.len())
            .map(|ri| {
                branches
                    .iter()
                    .filter(|&&(src, tgt)| ri > src && ri < tgt)
                    .count()
            })
            .max()
            .unwrap_or(0);
        // +1 for fuel check nesting inside branches.
        let max_depth = max_branch_depth + 1;

        let asm_width = compute_asm_width(func, &regions);
        // prefix_width at max depth:
        //   addr(4) + space(1) + depth*2 (parent pipes) + 4 (├─╮ ) = 9 + depth*2
        // We add asm_width + some padding for the IR column.
        let ir_col = 9 + 2 * max_depth + asm_width + 4;

        Self {
            func,
            func_name,
            regions,
            branches,
            label_at,
            ir_at,
            ir_col,
        }
    }
}

/// Render a single function as a tree of nested blocks.
///
/// Conditional branches (wasm if/else) and fuel checks are shown as
/// indented sub-blocks, mirroring the structure of a high-level program.
fn render_blocks_function(out: &mut String, name: &str, func: &FunctionOutput) {
    let ctx = TreeCtx::build(func, name);
    if ctx.regions.is_empty() {
        return;
    }

    writeln!(out, "     func {name}{}", format_signature(func.param_count, func.result_count)).unwrap();
    emit_separator(out, 0);

    render_tree(out, &ctx, 0, ctx.regions.len(), 0);

    emit_separator(out, 0);
    emit_header(out, 0, "end", "╰─", None, ctx.ir_col);
    writeln!(out).unwrap();
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

            // Show the actual branch instruction with ├─╮ connector.
            let branch_word_idx = region.end - 1;
            let branch_word = ctx.func.code[branch_word_idx];
            let raw_asm = normalize_asm(&decode_instruction(branch_word));

            // Resolve branch target label — search within the target region
            // since regalloc edits may shift the label away from region.start.
            let target_region = &ctx.regions[target];
            let target_label = (target_region.start..target_region.end)
                .find_map(|w| ctx.label_at.get(w).and_then(|l| l.as_deref()))
                .unwrap_or("?");
            let asm = rewrite_branch_target(&raw_asm, target_label);
            let ir_note = ctx.ir_at.get(branch_word_idx).and_then(|n| n.as_deref());

            emit_branch_open(
                out,
                branch_word_idx * 4,
                &asm,
                depth,
                ir_note,
                ctx.ir_col,
            );

            // Render fall-through body (the "then" path) at depth+1.
            render_tree(out, ctx, ri + 1, target, depth + 1);

            // Close with ╰─ end (the fall-through path always exits
            // via ret or branch before reaching the target label).
            emit_header(out, depth + 1, "end", "╰─", None, ctx.ir_col);

            ri = target;
            continue;
        }

        // No branch — render region's instructions normally.
        render_words(out, ctx, ctx.regions[ri].start, ctx.regions[ri].end, depth);
        ri += 1;
    }
}

/// Render machine code words[start..end] at the given depth, detecting
/// fuel checks and expanding them as nested blocks.
fn render_words(out: &mut String, ctx: &TreeCtx, start: usize, end: usize, depth: usize) {
    let mut wi = start;
    while wi < end {
        let word = ctx.func.code[wi];

        // Fuel check: subs x21, x21, #N followed by b.le
        if wi + 1 < end && is_fuel_subs(word) && is_b_le(ctx.func.code[wi + 1]) {
            // Emit the subs instruction as a normal line.
            let asm = normalize_asm(&decode_instruction(word));
            let ir = ctx.ir_at.get(wi).and_then(|n| n.as_deref());
            emit_line(out, wi * 4, &asm, depth, ir, ctx.ir_col);

            // Show the b.le instruction with ├─╮ to open the suspend block.
            let b_le = ctx.func.code[wi + 1];
            let raw_b_le = normalize_asm(&decode_instruction(b_le));
            let b_le_asm = rewrite_branch_target(&raw_b_le, "suspend");
            emit_branch_open(out, (wi + 1) * 4, &b_le_asm, depth, None, ctx.ir_col);

            // Render the cold stub inline at depth+1.
            let cold_off = branch_word_offset(b_le).unwrap();
            let cold_start = ((wi + 1) as i64 + cold_off as i64) as usize;
            render_cold_stub(out, ctx, cold_start, depth + 1);

            wi += 2;
            continue;
        }

        // Normal instruction — resolve bl targets to function names.
        let raw_asm = normalize_asm(&decode_instruction(word));
        let asm = if is_bl(word) {
            resolve_bl_target(&raw_asm, word, wi, ctx.func_name)
        } else {
            raw_asm
        };
        let ir = ctx.ir_at.get(wi).and_then(|n| n.as_deref());
        emit_line(out, wi * 4, &asm, depth, ir, ctx.ir_col);
        wi += 1;
    }
}

/// Render the two-instruction cold stub (bl yield_handler + b @resume),
/// closing the block with `╰─` on the final `b @resume` line.
fn render_cold_stub(out: &mut String, ctx: &TreeCtx, cold_start: usize, depth: usize) {
    // bl yield_handler — rewrite target to "yield".
    let word0 = ctx.func.code[cold_start];
    let raw0 = normalize_asm(&decode_instruction(word0));
    let asm0 = rewrite_branch_target(&raw0, "yield");
    emit_line(out, cold_start * 4, &asm0, depth, Some("suspend"), ctx.ir_col);

    // b @resume — close the block with ╰─ since this branch exits.
    let word1 = ctx.func.code[cold_start + 1];
    let raw1 = normalize_asm(&decode_instruction(word1));
    let resume_off = branch_word_offset(word1).unwrap();
    let resume_word = ((cold_start + 1) as i64 + resume_off as i64) as usize;
    let resume_label = format!("@{:04x}", resume_word * 4);
    let asm1 = rewrite_branch_target(&raw1, &resume_label);
    emit_block_end_line(out, (cold_start + 1) * 4, &asm1, depth, Some("resume"), ctx.ir_col);
}

// ---- Line rendering helpers ----

/// Build the pipe prefix for an instruction line at the given depth.
///
/// depth 0: `│  `   depth 1: `│ │  `   depth 2: `│ │ │  `
fn pipe_prefix(depth: usize) -> String {
    let mut s = String::with_capacity(2 * (depth + 1) + 1);
    for i in 0..=depth {
        s.push('│');
        if i < depth {
            s.push(' ');
        } else {
            s.push_str("  ");
        }
    }
    s
}

/// Build the pipe prefix for a header line (├─ or ╰─) at the given depth.
///
/// depth 0: `├─ `   depth 1: `│ ├─ `   depth 2: `│ │ ├─ `
fn header_prefix(depth: usize, connector: &str) -> String {
    let mut s = String::with_capacity(2 * depth + 3);
    for _ in 0..depth {
        s.push_str("│ ");
    }
    s.push_str(connector);
    s.push(' ');
    s
}

/// Build the prefix for a branch-opening line: `├─╮ `.
///
/// depth 0: `├─╮ `   depth 1: `│ ├─╮ `
fn branch_open_prefix(depth: usize) -> String {
    let mut s = String::with_capacity(2 * depth + 4);
    for _ in 0..depth {
        s.push_str("│ ");
    }
    s.push_str("├─╮ ");
    s
}


/// Build the pipe prefix for a blank separator line.
///
/// depth 0: `│`   depth 1: `│ │`   depth 2: `│ │ │`
fn separator_prefix(depth: usize) -> String {
    let mut s = String::with_capacity(2 * depth + 1);
    for i in 0..=depth {
        s.push('│');
        if i < depth {
            s.push(' ');
        }
    }
    s
}

/// Emit a single instruction line: `ADDR PIPES ASM [pad] IR`.
fn emit_line(out: &mut String, byte_off: usize, asm: &str, depth: usize, ir: Option<&str>, ir_col: usize) {
    let mut line = format!("{byte_off:04x} {}{asm}", pipe_prefix(depth));
    if let Some(note) = ir {
        if !note.is_empty() {
            pad_to(&mut line, ir_col, ' ');
            line.push_str(note);
        }
    }
    let trimmed = line.trim_end();
    writeln!(out, "{trimmed}").unwrap();
}

/// Emit a header line: `     PIPES CONNECTOR LABEL [pad] IR`.
fn emit_header(
    out: &mut String,
    depth: usize,
    label: &str,
    connector: &str,
    ir: Option<&str>,
    ir_col: usize,
) {
    let mut line = format!("     {}{label}", header_prefix(depth, connector));
    if let Some(note) = ir {
        if !note.is_empty() {
            pad_to(&mut line, ir_col, ' ');
            line.push_str(note);
        }
    }
    let trimmed = line.trim_end();
    writeln!(out, "{trimmed}").unwrap();
}

/// Emit a blank separator line with depth-appropriate pipes.
fn emit_separator(out: &mut String, depth: usize) {
    let line = format!("     {}", separator_prefix(depth));
    let trimmed = line.trim_end();
    writeln!(out, "{trimmed}").unwrap();
}

/// Emit a branch-opening line: `ADDR ├─╮ ASM [pad] IR`.
///
/// Shows the actual branch instruction with a `├─╮` connector that
/// visually opens a nested sub-block for the branch path.
fn emit_branch_open(
    out: &mut String,
    byte_off: usize,
    asm: &str,
    depth: usize,
    ir: Option<&str>,
    ir_col: usize,
) {
    let mut line = format!("{byte_off:04x} {}{asm}", branch_open_prefix(depth));
    if let Some(note) = ir {
        if !note.is_empty() {
            pad_to(&mut line, ir_col, ' ');
            line.push_str(note);
        }
    }
    let trimmed = line.trim_end();
    writeln!(out, "{trimmed}").unwrap();
}

/// Emit an instruction line that closes a block with `╰─`.
///
/// Like `emit_line` but the innermost pipe is replaced with `╰─`,
/// visually terminating the nested block on this instruction.
fn emit_block_end_line(
    out: &mut String,
    byte_off: usize,
    asm: &str,
    depth: usize,
    ir: Option<&str>,
    ir_col: usize,
) {
    // Build prefix: parent pipes for 0..depth, then ╰─
    let mut prefix = String::new();
    for _ in 0..depth {
        prefix.push_str("│ ");
    }
    prefix.push_str("╰─ ");

    let mut line = format!("{byte_off:04x} {prefix}{asm}");
    if let Some(note) = ir {
        if !note.is_empty() {
            pad_to(&mut line, ir_col, ' ');
            line.push_str(note);
        }
    }
    let trimmed = line.trim_end();
    writeln!(out, "{trimmed}").unwrap();
}


/// Rewrite a branch instruction's hex target with a human-readable name.
///
/// Given a decoded ASM string like `b.gt  0x18`, replaces the hex offset
/// with the provided label to produce `b.gt  L0`.
fn rewrite_branch_target(asm: &str, label: &str) -> String {
    // Find the last `0x` or `-0x` token and replace it with the label.
    if let Some(pos) = asm.rfind("0x") {
        // Check for a preceding `-` sign.
        let start = if pos > 0 && asm.as_bytes()[pos - 1] == b'-' {
            pos - 1
        } else {
            pos
        };
        // Find the end of the hex literal.
        let rest = &asm[pos + 2..];
        let hex_len = rest
            .find(|c: char| !c.is_ascii_hexdigit())
            .unwrap_or(rest.len());
        let end = pos + 2 + hex_len;
        format!("{}{label}{}", &asm[..start], &asm[end..])
    } else {
        asm.to_string()
    }
}

/// Build the word_idx → annotation map using source op labels.
///
/// Groups consecutive IR regions by their source parsed op. The
/// annotation is placed on the first word of the group's **last**
/// region — so that annotations like `call 0` appear on the actual
/// `bl` instruction rather than the preceding fuel check.
fn build_source_op_annotations(func: &FunctionOutput, regions: &[Region]) -> Vec<Option<String>> {
    let total_words = func.code.len();
    let mut annotations: Vec<Option<String>> = vec![None; total_words];

    // Region 0 is prologue — label it.
    if let Some(region) = regions.first() {
        if region.start < annotations.len() {
            annotations[region.start] = Some("prologue".into());
        }
    }

    let body_regions: Vec<&Region> = regions
        .iter()
        .filter(|r| r.marker_idx > 0)
        .collect();

    let mut i = 0;
    while i < body_regions.len() {
        let ir_idx = body_regions[i].marker_idx - 1;
        if ir_idx >= func.source_ops.len() {
            i += 1;
            continue;
        }
        let source_op = func.source_ops[ir_idx];

        // Find the extent of this group.
        let mut group_end = i + 1;
        while group_end < body_regions.len() {
            let idx = body_regions[group_end].marker_idx - 1;
            if idx >= func.source_ops.len() || func.source_ops[idx] != source_op {
                break;
            }
            group_end += 1;
        }

        let label = func
            .op_labels
            .get(source_op as usize)
            .map(|s| s.as_str())
            .unwrap_or("");

        if !label.is_empty() {
            // Annotate on the last region's first word — so fuel checks
            // don't steal the label from the actual instruction.
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

// ---- Data collection helpers ----

/// Collect non-empty regions from markers, up to `max_regions` region indices.
fn collect_regions(
    markers: &[usize],
    total_words: usize,
    max_regions: usize,
) -> Vec<Region> {
    let count = markers.len().min(max_regions);
    let mut regions = Vec::new();
    for region_idx in 0..count {
        let start = markers[region_idx];
        let end = if region_idx + 1 < markers.len() {
            markers[region_idx + 1]
        } else {
            total_words
        };
        if start == end {
            continue;
        }
        regions.push(Region {
            start,
            end,
            marker_idx: region_idx,
        });
    }
    regions
}

/// Find all forward conditional branches as (source_ri, target_ri) pairs.
fn find_forward_branches(regions: &[Region], code: &[u32]) -> Vec<(usize, usize)> {
    let mut branches = Vec::new();
    for (ri, region) in regions.iter().enumerate() {
        if region.end == region.start {
            continue;
        }
        let last_word = code[region.end - 1];
        if !is_conditional_branch(last_word) {
            continue;
        }
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
fn compute_asm_width(func: &FunctionOutput, regions: &[Region]) -> usize {
    let mut max_w = 0usize;
    for region in regions {
        for word_idx in region.start..region.end {
            let word = func.code[word_idx];
            let asm = normalize_asm(&decode_instruction(word));
            max_w = max_w.max(display_width(&asm));
        }
    }
    // Also check cold stub instructions (tail of code buffer).
    let body_end = regions.last().map(|r| r.end).unwrap_or(0);
    for wi in body_end..func.code.len() {
        let asm = normalize_asm(&decode_instruction(func.code[wi]));
        max_w = max_w.max(display_width(&asm));
    }
    max_w + 2
}

/// Expand tabs in decoded instructions to fixed-width spacing and
/// rename global registers to readable names.
///
/// `disarm64` outputs `mnemonic\t\toperands`. We replace the tab sequence
/// with spaces so operands always start at column 6, then rename special
/// registers: x21→g.fuel, x29→g.fp, x20→g.ctx, sp→g.sp, x30→g.lr.
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

/// Rename global/special registers in a decoded instruction string.
///
/// Only replaces register names at word boundaries (not inside hex
/// literals like `#0x29`). Register names replaced:
/// - x21 → g.fuel (fuel counter)
/// - x29 → g.fp (frame pointer)
/// - x20 → g.ctx (JIT context pointer)
/// - x30 → g.lr (link register)
/// - sp → g.sp (stack pointer, only in operand position)
fn rename_registers(s: &str) -> String {
    let mut result = s.to_string();
    // Replace longer names first to avoid partial matches.
    result = replace_at_word_boundary(&result, "x21", "g.fuel");
    result = replace_at_word_boundary(&result, "x29", "g.fp");
    result = replace_at_word_boundary(&result, "x20", "g.ctx");
    result = replace_at_word_boundary(&result, "x30", "g.lr");
    result = replace_at_word_boundary(&result, "sp", "g.sp");
    result
}

/// Replace `from` with `to` only when `from` appears at word boundaries.
///
/// A word boundary means the character before/after the match is not
/// ASCII-alphanumeric. This prevents `x29` matching inside `0x29` or
/// `sp` matching inside `stp`.
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

/// Compute the display width of a string (number of terminal columns).
///
/// Uses character count, which is correct for ASCII and the single-width
/// box-drawing characters we use (│, ├, ╰, ─, ╮, ╯, ▸).
fn display_width(s: &str) -> usize {
    s.chars().count()
}

/// Pad a string with `fill` characters until its display width reaches
/// `target_col`.
fn pad_to(s: &mut String, target_col: usize, fill: char) {
    let current = display_width(s);
    for _ in current..target_col {
        s.push(fill);
    }
}

/// Format a display-friendly signature with register names.
///
/// Uses the calling convention: params in x9, x10, x11, ...;
/// return value in x9.
fn format_signature(param_count: usize, result_count: usize) -> String {
    let param_list: Vec<String> = (0..param_count)
        .map(|i| format!("x{}: i32", 9 + i))
        .collect();
    let params = param_list.join(", ");
    let result_part = if result_count > 0 {
        " -> x9: i32"
    } else {
        ""
    };
    format!("({params}){result_part}")
}

/// Returns true if the word is a conditional branch (b.cond, cbz, cbnz).
fn is_conditional_branch(word: u32) -> bool {
    let top8 = word >> 24;
    matches!(top8, 0x54 | 0x34 | 0x35 | 0xB4 | 0xB5)
}

/// Returns true if the word is `subs x21, x21, #imm12`
/// (the fuel decrement instruction).
fn is_fuel_subs(word: u32) -> bool {
    // subs x21, x21, #imm12: sf=1 op=1 S=1 100010 sh=0 imm12 Rn=10101 Rd=10101
    (word & 0xFFC0_03FF) == 0xF100_02B5
}

/// Returns true if the word is `b.le` (condition code 0xD).
fn is_b_le(word: u32) -> bool {
    (word & 0xFF00_001F) == 0x5400_000D
}

/// Returns true if the word is a `bl` (branch with link) instruction.
fn is_bl(word: u32) -> bool {
    matches!(word >> 24, 0x94..=0x97)
}

/// Resolve a `bl` instruction's target to a function name.
///
/// If the target is word 0 (the function's own body start), it's a
/// self-recursive call. Otherwise, we show the raw target.
fn resolve_bl_target(asm: &str, word: u32, word_idx: usize, func_name: &str) -> String {
    if let Some(offset) = branch_word_offset(word) {
        let target = word_idx as i64 + offset as i64;
        if target == 0 {
            return rewrite_branch_target(asm, func_name);
        }
    }
    asm.to_string()
}
