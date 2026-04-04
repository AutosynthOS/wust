//! Grid state — tracks which vreg lives in which physical location.
//!
//! The grid is a `BTreeMap<SlotKey, VRegKey>`. It represents the
//! register/memory state at a point in the program. Operations
//! mutate the grid via micro-ops derived from their opcode.

use std::collections::BTreeMap;

use autosynth_isa::PReg;
use slotmap::SlotMap;

use crate::{
    VRegKey,
    types::{OpKey, Operation, SlotKey, VCode, VInit},
};

/// The grid state: a map from physical locations to the vreg occupying them.
pub type Grid = BTreeMap<SlotKey, VRegKey>;

const PREG_COUNT: u8 = 31;

/// Apply the effects of an operation to the grid state.
///
/// Each opcode has different micro-ops:
/// - param/const/load/alu: write defines into their assigned slots
/// - set_slot: write a vreg into a memory slot
/// - clear_slot: remove a memory slot entry
/// - call: clobber all pregs and vreg-space, then write defines
/// - brif/return: no grid effect
pub fn apply_micro_ops(
    grid: &mut Grid,
    op: &Operation,
    ops: &SlotMap<OpKey, Operation>,
    vregs: &SlotMap<VRegKey, VInit>,
) {
    match op.opcode {
        VCode::Define | VCode::Load(_) | VCode::Alu(_) => {
            write_defines(grid, op, vregs);
        }
        VCode::SetSlot(mem) => {
            // The vreg being stored: for the new builder pattern, input[1]
            // is a VReg (vref) and input[0] is an Op (oref). For the old
            // pattern, input[0] is a VReg. Try index 1 first, then 0.
            let vreg_key =
                resolve_vreg_input(op, 1, ops).or_else(|| resolve_vreg_input(op, 0, ops));
            if let Some(vreg_key) = vreg_key {
                grid.insert(SlotKey::Mem(mem), vreg_key);
            }
        }
        VCode::ClearSlot(mem) => {
            grid.remove(&SlotKey::Mem(mem));
        }
        VCode::Call { .. } => {
            // Clobber all pregs
            for i in 0..PREG_COUNT {
                grid.remove(&SlotKey::PReg(PReg(i)));
            }
            // Remove vreg-space entries
            let vreg_keys: Vec<SlotKey> = grid
                .keys()
                .filter(|k| matches!(k, SlotKey::VReg(_)))
                .copied()
                .collect();
            for k in vreg_keys {
                grid.remove(&k);
            }
            write_defines(grid, op, vregs);
        }
        VCode::Phi => {
            write_defines(grid, op, vregs);
        }
        VCode::BrIf | VCode::Return { .. } => {}
    }
}

/// Write an operation's defines into the grid.
///
/// For each defined vreg:
/// - If it has a preg hint, write to that preg slot
/// - If it has a constant, write to a const slot
/// - Otherwise write to vreg-space (unassigned)
fn write_defines(grid: &mut Grid, op: &Operation, vregs: &SlotMap<VRegKey, VInit>) {
    for &vreg_key in &op.defines {
        let Some(def) = vregs.get(vreg_key) else {
            continue;
        };
        if let Some(val) = def.constant {
            grid.insert(SlotKey::Const(val), vreg_key);
        } else if let Some(preg) = def.preg {
            grid.insert(SlotKey::PReg(preg), vreg_key);
        } else {
            grid.insert(SlotKey::VReg(vreg_key), vreg_key);
        }
    }
}

/// Resolve the vreg referenced by an input at the given index.
///
/// For `Input::Op`, we need the ops arena to trace through the
/// operation reference. When `ops` is not available (or for
/// set_slot/clear_slot micro-ops), we also check `Input::VReg`.
use crate::types::resolve_vreg_input;

/// Compute the grid state just before an operation executes.
///
/// Walks the prev chain upward to collect all predecessors, then
/// replays micro-ops forward from an empty grid.
pub fn get_slots_before(
    op_key: Option<OpKey>,
    ops: &SlotMap<OpKey, Operation>,
    vregs: &SlotMap<VRegKey, VInit>,
) -> Grid {
    let op_key = match op_key {
        None => return Grid::new(),
        Some(key) => key,
    };

    let Some(op) = ops.get(op_key) else {
        return Grid::new();
    };
    // Collect the chain of predecessors (not including op_key itself)
    let mut chain = Vec::new();
    let mut cur = op.prev;
    while let Some(prev_key) = cur {
        chain.push(prev_key);
        cur = ops.get(prev_key).and_then(|o| o.prev);
    }
    chain.reverse();

    // Replay micro-ops forward
    let mut grid = Grid::new();
    for &key in &chain {
        if let Some(prev_op) = ops.get(key) {
            apply_micro_ops(&mut grid, prev_op, ops, vregs);
        }
    }
    grid
}

/// Compute the grid state after an operation executes.
///
/// Same as get_slots_before but includes the operation itself.
pub fn get_slots_after(
    op_key: OpKey,
    ops: &SlotMap<OpKey, Operation>,
    vregs: &SlotMap<VRegKey, VInit>,
) -> Grid {
    let mut grid = get_slots_before(Some(op_key), ops, vregs);
    if let Some(op) = ops.get(op_key) {
        apply_micro_ops(&mut grid, op, ops, vregs);
    }
    grid
}
