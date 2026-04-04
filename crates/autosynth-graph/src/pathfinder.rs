//! Pathfinder — resolves register allocation by finding where vregs live
//! in the grid state and emitting loads, assigning pregs, or rewriting
//! operands as needed.
//!
//! The pathfinder walks the sorted operation list. For each operation it:
//! 1. Computes what the operation requires (contracts).
//! 2. Checks if each contract is already satisfied by the grid state.
//! 3. If not, finds the vreg via `find_path` and resolves:
//!    - vreg-space → assign a preg to the defining op
//!    - mem slot → emit a load before the consumer, rewrite the input
//! 4. Rewrites remaining operands to point at valid source operations.

use std::collections::HashSet;

use autosynth_isa::{PReg, Width};
use slotmap::SlotMap;
use smallvec::smallvec;

use crate::grid::{self, Grid};
use crate::types::{Input, MemSlot, OpCode, OpKey, Operation, SlotKey, VRegDef, VRegKey};

const PREG_COUNT: u8 = 31;

/// Where a vreg was found and the cost to use it from there.
pub struct PathResult {
    pub vreg_key: VRegKey,
    pub found_in: SlotKey,
    pub cost: u32,
}

/// Cost of using a vreg from a given location.
fn slot_cost(found_in: SlotKey, target_slot: Option<SlotKey>) -> u32 {
    match found_in {
        SlotKey::VReg(_) => 0,
        SlotKey::PReg(p) => {
            if target_slot == Some(SlotKey::PReg(p)) {
                0
            } else {
                1
            }
        }
        SlotKey::Mem(_) => 4,
        SlotKey::Const(_) => 1,
    }
}

/// Find where a vreg lives in an already-computed grid state.
///
/// Scans every slot in the grid for entries holding `target_vreg`.
/// Returns the lowest-cost location.
fn find_path_in_grid(
    grid: &Grid,
    target_slot: Option<SlotKey>,
    target_vreg: VRegKey,
) -> Option<PathResult> {
    let mut best: Option<PathResult> = None;

    for (&slot_key, &vreg_key) in grid {
        if vreg_key != target_vreg {
            continue;
        }
        let cost = slot_cost(slot_key, target_slot);
        let is_better = match &best {
            None => true,
            Some(b) => cost < b.cost,
        };
        if is_better {
            best = Some(PathResult {
                vreg_key: target_vreg,
                found_in: slot_key,
                cost,
            });
        }
    }

    best
}

/// Find the first free physical register in the grid state.
fn find_free_preg(grid: &Grid) -> Option<PReg> {
    for i in 0..PREG_COUNT {
        let preg = PReg(i);
        if !grid.contains_key(&SlotKey::PReg(preg)) {
            return Some(preg);
        }
    }
    None
}

/// Check if a "need any preg" contract is satisfied: the vreg is in some preg.
fn is_in_any_preg(grid: &Grid, vreg_key: VRegKey) -> bool {
    grid.iter().any(|(slot_key, &v)| {
        v == vreg_key && matches!(slot_key, SlotKey::PReg(_))
    })
}

/// Check if a specific preg contract is satisfied: the vreg is in that exact preg.
fn is_in_preg(grid: &Grid, preg: PReg, vreg_key: VRegKey) -> bool {
    grid.get(&SlotKey::PReg(preg)) == Some(&vreg_key)
}

/// A contract that an operation requires to be satisfied.
/// Tracks the input index so we can rewrite it after resolution.
enum Contract {
    /// Vreg must be in a specific preg (e.g. w0 for call/return).
    SpecificPreg { input_idx: usize, vreg_key: VRegKey, preg: PReg },
    /// Vreg must be in any preg (ALU operands, set_slot values).
    AnyPreg { input_idx: usize, vreg_key: VRegKey },
}

/// Compute the contracts for an operation.
fn compute_contracts(
    op: &Operation,
    ops: &SlotMap<OpKey, Operation>,
    vregs: &SlotMap<VRegKey, VRegDef>,
) -> Vec<Contract> {
    let mut contracts = Vec::new();
    match op.opcode {
        OpCode::Call(_) | OpCode::Return => {
            if let Some(vreg_key) = resolve_input_vreg_skip_const(&op.inputs[0], ops, vregs) {
                contracts.push(Contract::SpecificPreg {
                    input_idx: 0,
                    vreg_key,
                    preg: PReg(0),
                });
            }
        }
        OpCode::Alu(_) | OpCode::BrIf => {
            for (i, input) in op.inputs.iter().enumerate() {
                if let Some(vreg_key) = resolve_input_vreg_skip_const(input, ops, vregs) {
                    contracts.push(Contract::AnyPreg { input_idx: i, vreg_key });
                }
            }
        }
        OpCode::SetSlot(_) => {
            // For the new builder pattern, the vreg is at input[1] (vref).
            // For the old pattern, it's at input[0].
            for (i, input) in op.inputs.iter().enumerate() {
                if let Some(vreg_key) = resolve_input_vreg_skip_const(input, ops, vregs) {
                    contracts.push(Contract::AnyPreg { input_idx: i, vreg_key });
                    break;
                }
            }
        }
        _ => {}
    }
    contracts
}

/// Resolve an input to the vreg key it references, skipping constants and imms.
fn resolve_input_vreg_skip_const(
    input: &Input,
    ops: &SlotMap<OpKey, Operation>,
    vregs: &SlotMap<VRegKey, VRegDef>,
) -> Option<VRegKey> {
    let vreg_key = match input {
        Input::VReg(key) => Some(*key),
        Input::Op(_) => crate::types::resolve_input_vreg(input, ops),
        Input::Imm12(_) => None,
    }?;
    if let Some(def) = vregs.get(vreg_key) {
        if def.constant.is_some() {
            return None;
        }
    }
    Some(vreg_key)
}

/// Assign a preg to a vreg's definition.
///
/// If `required` is Some, use that specific preg. Otherwise find a
/// free preg in the grid state before the defining operation.
fn assign_preg(
    vreg_key: VRegKey,
    required: Option<PReg>,
    ops: &SlotMap<OpKey, Operation>,
    vregs: &mut SlotMap<VRegKey, VRegDef>,
) -> bool {
    let Some(def) = vregs.get(vreg_key) else {
        return false;
    };
    let definer = def.definer;

    let preg = if let Some(p) = required {
        p
    } else {
        let grid = grid::get_slots_before(definer, ops, vregs);
        let Some(p) = find_free_preg(&grid) else {
            return false;
        };
        p
    };

    if let Some(def) = vregs.get_mut(vreg_key) {
        def.preg = Some(preg);
        true
    } else {
        false
    }
}

/// Insert a load operation before `consumer_key`.
///
/// Creates a new load op and vreg, then patches the prev chain:
/// `new_load.prev = consumer.prev; consumer.prev = new_load_key`.
///
/// Returns (load_op_key, load_vreg_key) so the caller can rewrite
/// the consumer's input to reference the load's vreg.
fn emit_load(
    consumer_key: OpKey,
    vreg_key: VRegKey,
    mem: MemSlot,
    ops: &mut SlotMap<OpKey, Operation>,
    vregs: &mut SlotMap<VRegKey, VRegDef>,
) -> Option<(OpKey, VRegKey)> {
    let grid = grid::get_slots_before(consumer_key, ops, vregs);
    let free = find_free_preg(&grid)?;

    // Find the store that wrote this vreg to this mem slot.
    let store_key = find_store(consumer_key, mem, vreg_key, ops);

    let consumer_prev = ops.get(consumer_key)?.prev;

    // Find the most recent side-effecting op to depend on.
    // Prefer the store, but fall back to walking the prev chain
    // for the most recent effect-producing op.
    let effect_dep = store_key.or_else(|| find_last_effect(consumer_key, ops));

    // Create the load operation and its vreg
    let load_key = ops.insert_with_key(|_key| Operation {
        opcode: OpCode::Load(mem),
        inputs: smallvec![],
        effect: effect_dep,
        prev: consumer_prev,
        defines: smallvec![],
    });

    let load_vreg = vregs.insert(VRegDef {
        width: Width::W32,
        definer: load_key,
        constant: None,
        preg: Some(free),
        mem: Some(mem),
    });
    ops[load_key].defines = smallvec![load_vreg];

    // Patch prev chain: consumer now follows the load
    ops[consumer_key].prev = Some(load_key);

    Some((load_key, load_vreg))
}

/// Walk backwards via prev to find the most recent side-effecting operation.
fn find_last_effect(
    from: OpKey,
    ops: &SlotMap<OpKey, Operation>,
) -> Option<OpKey> {
    let mut cur = ops.get(from)?.prev;
    while let Some(key) = cur {
        let op = ops.get(key)?;
        match op.opcode {
            OpCode::Call(_) | OpCode::SetSlot(_) | OpCode::Load(_) => return Some(key),
            _ => {}
        }
        cur = op.prev;
    }
    None
}

/// Walk backwards via prev to find a set_slot that wrote `vreg_key` to `mem`.
fn find_store(
    from: OpKey,
    mem: MemSlot,
    vreg_key: VRegKey,
    ops: &SlotMap<OpKey, Operation>,
) -> Option<OpKey> {
    let mut cur = ops.get(from)?.prev;
    while let Some(key) = cur {
        let op = ops.get(key)?;
        if op.opcode == OpCode::SetSlot(mem) {
            // Try input[1] first (new builder: oref + vref), then input[0] (old builder: vref).
            let stored_vreg = resolve_vreg_input(op, 1, ops)
                .or_else(|| resolve_vreg_input(op, 0, ops));
            if stored_vreg == Some(vreg_key) {
                return Some(key);
            }
        }
        cur = op.prev;
    }
    None
}

/// Resolve the vreg referenced by an operation's input at the given index.
fn resolve_vreg_input(
    op: &Operation,
    index: usize,
    ops: &SlotMap<OpKey, Operation>,
) -> Option<VRegKey> {
    match op.inputs.get(index) {
        Some(Input::VReg(k)) => Some(*k),
        Some(input @ Input::Op(_)) => crate::types::resolve_input_vreg(input, ops),
        _ => None,
    }
}

/// Walk backwards via prev to find the operation that defines a vreg.
fn find_defining_op(
    from: OpKey,
    vreg_key: VRegKey,
    ops: &SlotMap<OpKey, Operation>,
) -> Option<OpKey> {
    let mut cur = Some(from);
    while let Some(key) = cur {
        let op = ops.get(key)?;
        if op.defines.contains(&vreg_key) {
            return Some(key);
        }
        cur = op.prev;
    }
    None
}

/// Find the source operation for a vreg: the defining op (for preg/vreg)
/// or the store op (for mem).
fn find_source_op(
    op_key: OpKey,
    vreg_key: VRegKey,
    ops: &SlotMap<OpKey, Operation>,
    vregs: &SlotMap<VRegKey, VRegDef>,
) -> Option<OpKey> {
    let grid = grid::get_slots_before(op_key, ops, vregs);
    let path = find_path_in_grid(&grid, None, vreg_key)?;

    match path.found_in {
        SlotKey::Mem(mem) => find_store(op_key, mem, vreg_key, ops),
        _ => find_defining_op(op_key, vreg_key, ops),
    }
}

/// Rewrite operands on an operation to point at their valid source.
///
/// Two kinds of rewrites:
/// 1. `Input::Op` → `Input::VReg`: resolve the op reference to the
///    underlying vreg, breaking the ordering dependency on the
///    set_slot/clear_slot chain so the sweep can remove it.
/// 2. VReg source changed: if the pathfinder inserted a load that
///    defines a new vreg for the same logical value, rewrite to use
///    the load's vreg.
fn rewrite_operands(
    op_key: OpKey,
    ops: &mut SlotMap<OpKey, Operation>,
    vregs: &SlotMap<VRegKey, VRegDef>,
) {
    // Collect rewrite targets first to avoid borrow conflicts
    let rewrites: Vec<(usize, VRegKey)> = {
        let Some(op) = ops.get(op_key) else { return };
        let mut result = Vec::new();
        for (i, input) in op.inputs.iter().enumerate() {
            let (vreg_key, is_op_ref) = match input {
                Input::VReg(k) => (*k, false),
                Input::Op(_) => {
                    match crate::types::resolve_input_vreg(input, ops) {
                        Some(k) => (k, true),
                        None => continue,
                    }
                }
                Input::Imm12(_) => continue,
            };
            // Skip constants
            if let Some(def) = vregs.get(vreg_key) {
                if def.constant.is_some() {
                    // Still rewrite Op→VReg for constants to break
                    // the ordering dependency.
                    if is_op_ref {
                        result.push((i, vreg_key));
                    }
                    continue;
                }
            }
            // For Op refs, find the best source and rewrite to VReg.
            // For VReg refs, only rewrite if the source changed.
            let Some(source_key) = find_source_op(op_key, vreg_key, ops, vregs) else {
                // No source found — if it's an Op ref, at least
                // rewrite to the resolved vreg.
                if is_op_ref {
                    result.push((i, vreg_key));
                }
                continue;
            };
            let Some(source_op) = ops.get(source_key) else {
                if is_op_ref {
                    result.push((i, vreg_key));
                }
                continue;
            };
            if let Some(&new_vreg) = source_op.defines.first() {
                if new_vreg != vreg_key || is_op_ref {
                    result.push((i, new_vreg));
                }
            } else if is_op_ref {
                result.push((i, vreg_key));
            }
        }
        result
    };

    for (i, new_vreg) in rewrites {
        if let Some(op) = ops.get_mut(op_key) {
            op.inputs[i] = Input::VReg(new_vreg);
        }
    }
}

/// Run the pathfinder over all operations: resolve contracts, insert
/// loads, assign pregs, and rewrite operands.
///
/// Returns the number of changes applied. Call repeatedly (re-collecting
/// nodes between passes) until it returns 0.
pub fn apply_paths(
    sorted: &[OpKey],
    ops: &mut SlotMap<OpKey, Operation>,
    vregs: &mut SlotMap<VRegKey, VRegDef>,
) -> u32 {
    // Pre-scan: build a map of vreg → required preg for all SpecificPreg
    // contracts. When an AnyPreg assignment encounters a vreg with a
    // downstream SpecificPreg requirement, it uses that preg directly —
    // no wasted register, no mov needed.
    let mut preg_hints: std::collections::HashMap<VRegKey, PReg> = std::collections::HashMap::new();
    for &op_key in sorted {
        let Some(op) = ops.get(op_key) else { continue };
        for contract in compute_contracts(op, ops, vregs) {
            if let Contract::SpecificPreg { vreg_key, preg, .. } = contract {
                preg_hints.insert(vreg_key, preg);
            }
        }
    }

    let mut applied = 0u32;
    let mut assigned: HashSet<VRegKey> = HashSet::new();

    for &op_key in sorted {
        let Some(op) = ops.get(op_key) else { continue };
        if op.prev.is_none() { continue; }

        let contracts = compute_contracts(op, ops, vregs);

        for contract in &contracts {
            // Recompute grid each time — previous contract resolutions
            // may have changed prev chain (load insertions).
            let prev_key = ops.get(op_key).and_then(|o| o.prev);
            let Some(prev_key) = prev_key else { continue };
            let prev_grid = grid::get_slots_after(prev_key, ops, vregs);

            match contract {
                Contract::SpecificPreg { input_idx, vreg_key, preg } => {
                    if is_in_preg(&prev_grid, *preg, *vreg_key) {
                        continue;
                    }
                    let path = find_path_in_grid(
                        &prev_grid,
                        Some(SlotKey::PReg(*preg)),
                        *vreg_key,
                    );
                    let Some(path) = path else { continue };

                    match path.found_in {
                        SlotKey::VReg(_) => {
                            if assign_preg(*vreg_key, Some(*preg), ops, vregs) {
                                assigned.insert(*vreg_key);
                                applied += 1;
                            }
                        }
                        SlotKey::Mem(mem) => {
                            if let Some((_load_key, load_vreg)) =
                                emit_load(op_key, *vreg_key, mem, ops, vregs)
                            {
                                ops[op_key].inputs[*input_idx] = Input::VReg(load_vreg);
                                applied += 1;
                            }
                        }
                        _ => {}
                    }
                }
                Contract::AnyPreg { input_idx, vreg_key } => {
                    if is_in_any_preg(&prev_grid, *vreg_key) {
                        continue;
                    }
                    let path = find_path_in_grid(&prev_grid, None, *vreg_key);
                    let Some(path) = path else { continue };

                    let is_already_assigned = assigned.contains(vreg_key);
                    match path.found_in {
                        SlotKey::VReg(_) if !is_already_assigned => {
                            // Use the preg hint if this vreg has a downstream
                            // SpecificPreg requirement (e.g. call needs w0).
                            let hint = preg_hints.get(vreg_key).copied();
                            if assign_preg(*vreg_key, hint, ops, vregs) {
                                assigned.insert(*vreg_key);
                                applied += 1;
                            }
                        }
                        SlotKey::Mem(mem) => {
                            if let Some((_load_key, load_vreg)) =
                                emit_load(op_key, *vreg_key, mem, ops, vregs)
                            {
                                // Rewrite the consumer's input to use the load's vreg
                                ops[op_key].inputs[*input_idx] = Input::VReg(load_vreg);
                                applied += 1;
                            }
                        }
                        _ => {}
                    }
                }
            }
        }

        rewrite_operands(op_key, ops, vregs);
    }

    applied
}

/// Re-collect the sorted operation list by walking prev chains from roots.
///
/// After the pathfinder inserts loads (which patch prev pointers),
/// the original sorted list is stale. This walks from each root
/// backwards via prev, then returns operations in forward order.
pub fn collect_nodes(
    roots: &[OpKey],
    ops: &SlotMap<OpKey, Operation>,
) -> Vec<OpKey> {
    let mut seen = HashSet::new();
    let mut result = Vec::new();

    fn walk(
        key: OpKey,
        ops: &SlotMap<OpKey, Operation>,
        seen: &mut HashSet<OpKey>,
        result: &mut Vec<OpKey>,
    ) {
        if !seen.insert(key) {
            return;
        }
        if let Some(op) = ops.get(key) {
            if let Some(prev) = op.prev {
                walk(prev, ops, seen, result);
            }
        }
        result.push(key);
    }

    for &root in roots {
        walk(root, ops, &mut seen, &mut result);
    }

    result
}
