//! Display formatting for the graph IR.
//!
//! Produces colored terminal output showing the timeline with
//! blocks, operations, and grid states.

use autosynth_isa::{PReg, Width};
use slotmap::{Key, SlotMap};

use crate::grid::{self, Grid};
use crate::timeline::Block;
use crate::types::{Input, OpCode, OpKey, Operation, SlotKey, VRegDef, VRegKey};

/// ANSI color codes.
mod color {
    pub const RESET: &str = "\x1b[0m";
    pub const DIM: &str = "\x1b[2m";
    pub const BOLD: &str = "\x1b[1m";
    pub const RED: &str = "\x1b[31m";
    pub const YELLOW: &str = "\x1b[33m";
    pub const MAGENTA: &str = "\x1b[35m";
    pub const GRAY: &str = "\x1b[38;5;245m";
    pub const BROWN: &str = "\x1b[38;5;130m";
    pub const ORANGE: &str = "\x1b[38;5;208m";
}

/// Format a physical register with its width prefix.
pub fn fmt_preg(preg: PReg, width: Width) -> String {
    match width {
        Width::W32 => format!("w{}", preg.0),
        Width::W64 => format!("x{}", preg.0),
    }
}

/// Format a vreg name like "v0", "v1", etc.
///
/// Uses the slotmap key's version-less index for a stable human ID.
fn fmt_vreg(key: VRegKey) -> String {
    // SlotMap KeyData: lower 32 bits = index, upper 32 bits = version
    let ffi = key.data().as_ffi();
    let idx = ffi & 0xFFFF_FFFF;
    format!("v{idx}")
}

/// Format a vreg with its preg location if known.
fn fmt_vreg_with_preg(
    key: VRegKey,
    vregs: &SlotMap<VRegKey, VRegDef>,
    before: Option<&Grid>,
) -> String {
    let name = fmt_vreg(key);
    // Check if this vreg is in a preg in the grid
    if let Some(grid) = before {
        for (&slot_key, &slot_vreg) in grid {
            if slot_vreg == key {
                if let SlotKey::PReg(preg) = slot_key {
                    let width = vregs.get(key).map(|d| d.width).unwrap_or(Width::W32);
                    return format!(
                        "{DIM}{name}{RESET}:{MAG}{preg}{RESET}",
                        DIM = color::DIM,
                        RESET = color::RESET,
                        MAG = color::MAGENTA,
                        preg = fmt_preg(preg, width),
                    );
                }
            }
        }
    }
    // Vreg not in a preg — show in red (unallocated)
    format!("{RED}{name}{RESET}", RED = color::RED, RESET = color::RESET)
}

/// Format an input operand for display.
fn fmt_input(
    input: &Input,
    vregs: &SlotMap<VRegKey, VRegDef>,
    before: Option<&Grid>,
) -> String {
    match input {
        Input::VReg(key) => {
            // Check if it's a constant vreg
            if let Some(def) = vregs.get(*key) {
                if let Some(val) = def.constant {
                    return format!(
                        "{YELLOW}#{val}{RESET}",
                        YELLOW = color::YELLOW,
                        RESET = color::RESET,
                    );
                }
            }
            fmt_vreg_with_preg(*key, vregs, before)
        }
        Input::Imm12(imm) => {
            format!(
                "{YELLOW}#{val}{RESET}",
                YELLOW = color::YELLOW,
                val = imm.value(),
                RESET = color::RESET,
            )
        }
    }
}

/// Format a single operation for display.
pub fn fmt_op(
    op_key: OpKey,
    ops: &SlotMap<OpKey, Operation>,
    vregs: &SlotMap<VRegKey, VRegDef>,
    before: Option<&Grid>,
) -> String {
    let Some(op) = ops.get(op_key) else {
        return format!("{DIM}???{RESET}", DIM = color::DIM, RESET = color::RESET);
    };

    // Format defines
    let defs_str = format_defines(op, vregs);
    let defs_prefix = if defs_str.is_empty() {
        String::new()
    } else {
        format!("{defs_str} {DIM}={RESET} ", DIM = color::DIM, RESET = color::RESET)
    };

    // Format opcode
    let opcode_str = format_opcode(op.opcode);

    // Format operands
    let operands: Vec<String> = op
        .inputs
        .iter()
        .map(|i| fmt_input(i, vregs, before))
        .collect();
    let operands_str = operands.join(", ");

    // Format effect chain
    let effect_str = match op.effect {
        Some(eff_key) => {
            let eff_name = ops
                .get(eff_key)
                .map(|e| format_opcode_name(e.opcode))
                .unwrap_or_else(|| "???".to_string());
            format!(
                " {DIM}[after {name}]{RESET}",
                DIM = color::DIM,
                name = eff_name,
                RESET = color::RESET,
            )
        }
        None => String::new(),
    };

    format!("{defs_prefix}{BOLD}{opcode}{RESET}({operands}){effect}",
        BOLD = color::BOLD,
        opcode = opcode_str,
        RESET = color::RESET,
        operands = operands_str,
        effect = effect_str,
    )
}

/// Format the defines of an operation.
fn format_defines(op: &Operation, vregs: &SlotMap<VRegKey, VRegDef>) -> String {
    let parts: Vec<String> = op
        .defines
        .iter()
        .map(|&vreg_key| {
            let name = fmt_vreg(vreg_key);
            let Some(def) = vregs.get(vreg_key) else {
                return format!("{RED}{name}{RESET}", RED = color::RED, RESET = color::RESET);
            };
            if let Some(preg) = def.preg {
                let preg_str = fmt_preg(preg, def.width);
                format!(
                    "{GRAY}{name}{RESET}:{MAG}{preg}{RESET}",
                    GRAY = color::GRAY,
                    RESET = color::RESET,
                    MAG = color::MAGENTA,
                    preg = preg_str,
                )
            } else {
                format!("{RED}{name}{RESET}", RED = color::RED, RESET = color::RESET)
            }
        })
        .collect();
    parts.join(", ")
}

/// Format an opcode for display (just the name part).
fn format_opcode(opcode: OpCode) -> String {
    match opcode {
        OpCode::SetSlot(mem) => format!("set_slot {}", mem),
        OpCode::ClearSlot(mem) => format!("clear_slot {}", mem),
        OpCode::Load(mem) => format!("load {}", mem),
        OpCode::Call(idx) => format!("call ${idx}"),
        _ => opcode.name().to_string(),
    }
}

/// Format just the opcode name (for effect chain references).
fn format_opcode_name(opcode: OpCode) -> String {
    match opcode {
        OpCode::Call(idx) => format!("call ${idx}"),
        _ => opcode.name().to_string(),
    }
}

/// Format the grid state for display.
pub fn fmt_grid(
    grid: &Grid,
    vregs: &SlotMap<VRegKey, VRegDef>,
) -> String {
    let parts: Vec<String> = grid
        .iter()
        .map(|(&slot_key, &vreg_key)| {
            let name = fmt_vreg(vreg_key);
            let slot_str = format_slot_key(slot_key, vregs);
            if slot_str == name {
                // Vreg in vreg-space — show in red
                format!("{RED}{name}{RESET}", RED = color::RED, RESET = color::RESET)
            } else {
                let slot_color = match slot_key {
                    SlotKey::PReg(_) => color::MAGENTA,
                    SlotKey::Mem(_) => color::BROWN,
                    SlotKey::Const(_) => color::ORANGE,
                    SlotKey::VReg(_) => color::RED,
                };
                format!(
                    "{COLOR}{slot}{RESET}={GRAY}{name}{RESET}",
                    COLOR = slot_color,
                    slot = slot_str,
                    RESET = color::RESET,
                    GRAY = color::GRAY,
                )
            }
        })
        .collect();
    parts.join(", ")
}

/// Format a slot key for display.
fn format_slot_key(key: SlotKey, _vregs: &SlotMap<VRegKey, VRegDef>) -> String {
    match key {
        SlotKey::PReg(preg) => {
            // Default to w prefix (W32) — could be refined
            format!("w{}", preg.0)
        }
        SlotKey::Mem(mem) => format!("[x{}+{}]", mem.base.0, mem.offset),
        SlotKey::Const(val) => format!("c#{val}"),
        SlotKey::VReg(key) => fmt_vreg(key),
    }
}

/// Strip ANSI escape codes and return the visible length.
fn visible_len(s: &str) -> usize {
    let mut len = 0;
    let mut in_escape = false;
    for ch in s.chars() {
        if ch == '\x1b' {
            in_escape = true;
        } else if in_escape {
            if ch == 'm' {
                in_escape = false;
            }
        } else {
            len += 1;
        }
    }
    len
}

/// Print the full timeline with blocks and slot states.
pub fn print_timeline(
    label: &str,
    blocks: &[Block],
    ops: &SlotMap<OpKey, Operation>,
    vregs: &SlotMap<VRegKey, VRegDef>,
) {
    println!(
        "\n{BOLD}=== {label} ==={RESET}",
        BOLD = color::BOLD,
        RESET = color::RESET,
    );

    // First pass: compute max visible width
    let mut max_width = 0;
    for block in blocks {
        for (i, &op_key) in block.ops.iter().enumerate() {
            let before = grid::get_slots_before(op_key, ops, vregs);
            let line = format!(
                "  [{order:>2}] {op}",
                order = i + 1,
                op = fmt_op(op_key, ops, vregs, Some(&before)),
            );
            max_width = max_width.max(visible_len(&line));
        }
    }

    // Second pass: print with aligned slot states
    let mut global_order = 0;
    for block in blocks {
        println!(
            "  {DIM}--- {label} ---{RESET}",
            DIM = color::DIM,
            label = block.label,
            RESET = color::RESET,
        );
        for &op_key in &block.ops {
            global_order += 1;
            let before = grid::get_slots_before(op_key, ops, vregs);
            let after = grid::get_slots_after(op_key, ops, vregs);
            let line = format!(
                "  {DIM}[{order:>2}]{RESET} {op}",
                DIM = color::DIM,
                order = global_order,
                RESET = color::RESET,
                op = fmt_op(op_key, ops, vregs, Some(&before)),
            );
            let grid_str = fmt_grid(&after, vregs);
            if !grid_str.is_empty() {
                let vis = visible_len(&line);
                let padding = if max_width > vis {
                    max_width - vis + 4
                } else {
                    2
                };
                println!(
                    "{line}{pad}{DIM}||>{RESET} {grid}",
                    pad = " ".repeat(padding),
                    DIM = color::DIM,
                    RESET = color::RESET,
                    grid = grid_str,
                );
            } else {
                println!("{line}");
            }
        }
    }
}
