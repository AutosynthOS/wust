//! Timeline construction — topological sort, prev linking, block detection.
//!
//! The timeline is the sequential order of operations. It's computed
//! by topological sort over operand + effect edges, then prev pointers
//! are set so each operation knows its immediate predecessor.

use std::collections::HashSet;

use slotmap::SlotMap;

use crate::types::{Input, OpKey, Operation, VRegDef, VRegKey};

/// A block of operations sharing a control-flow context.
#[derive(Debug)]
pub struct Block {
    pub label: String,
    pub ops: Vec<OpKey>,
}

/// Find all operations reachable from the given roots by walking
/// operand and effect edges.
pub fn collect_reachable(
    roots: &[OpKey],
    ops: &SlotMap<OpKey, Operation>,
    vregs: &SlotMap<VRegKey, VRegDef>,
) -> HashSet<OpKey> {
    let mut visited = HashSet::new();
    for &root in roots {
        walk_reachable(root, ops, vregs, &mut visited);
    }
    visited
}

fn walk_reachable(
    key: OpKey,
    ops: &SlotMap<OpKey, Operation>,
    vregs: &SlotMap<VRegKey, VRegDef>,
    visited: &mut HashSet<OpKey>,
) {
    if !visited.insert(key) {
        return;
    }
    let Some(op) = ops.get(key) else { return };
    for input in &op.inputs {
        if let Input::VReg(vreg_key) = input {
            if let Some(def) = vregs.get(*vreg_key) {
                walk_reachable(def.definer, ops, vregs, visited);
            }
        }
    }
    if let Some(effect) = op.effect {
        walk_reachable(effect, ops, vregs, visited);
    }
}

/// Topologically sort reachable operations and set prev pointers.
///
/// Uses post-order DFS: dependencies (operands + effects) are visited
/// before the operation that uses them. After sorting, each operation's
/// `prev` is set to the immediately preceding operation in the order.
pub fn topo_sort_and_link(
    roots: &[OpKey],
    ops: &mut SlotMap<OpKey, Operation>,
    vregs: &SlotMap<VRegKey, VRegDef>,
) -> Vec<OpKey> {
    let reachable = collect_reachable(roots, ops, vregs);
    let mut sorted = Vec::with_capacity(reachable.len());
    let mut visited = HashSet::new();

    // Visit roots in order to get deterministic output
    for &root in roots {
        topo_visit(root, ops, vregs, &reachable, &mut visited, &mut sorted);
    }

    // Set prev pointers
    for i in 0..sorted.len() {
        let prev = if i > 0 { Some(sorted[i - 1]) } else { None };
        if let Some(op) = ops.get_mut(sorted[i]) {
            op.prev = prev;
        }
    }

    sorted
}

fn topo_visit(
    key: OpKey,
    ops: &SlotMap<OpKey, Operation>,
    vregs: &SlotMap<VRegKey, VRegDef>,
    reachable: &HashSet<OpKey>,
    visited: &mut HashSet<OpKey>,
    output: &mut Vec<OpKey>,
) {
    if !reachable.contains(&key) || !visited.insert(key) {
        return;
    }
    let Some(op) = ops.get(key) else { return };
    // Clone inputs/effect to avoid borrow conflict
    let inputs: Vec<Input> = op.inputs.to_vec();
    let effect = op.effect;

    // Visit effect chain first — side-effect ordering takes priority
    if let Some(effect_key) = effect {
        topo_visit(effect_key, ops, vregs, reachable, visited, output);
    }
    for input in &inputs {
        if let Input::VReg(vreg_key) = input {
            if let Some(def) = vregs.get(*vreg_key) {
                topo_visit(def.definer, ops, vregs, reachable, visited, output);
            }
        }
    }
    output.push(key);
}

/// Detect blocks by reachability from each terminal.
///
/// Operations reachable from ALL terminals are placed in "Entry".
/// Operations reachable from only one terminal are placed in "Case(N)".
pub fn detect_blocks(
    sorted: &[OpKey],
    terminals: &[OpKey],
    ops: &SlotMap<OpKey, Operation>,
    vregs: &SlotMap<VRegKey, VRegDef>,
) -> Vec<Block> {
    // Compute reachability from each terminal independently
    let per_terminal: Vec<HashSet<OpKey>> = terminals
        .iter()
        .map(|&t| {
            let mut set = HashSet::new();
            walk_reachable(t, ops, vregs, &mut set);
            set
        })
        .collect();

    let mut entry_ops = Vec::new();
    let mut case_ops: Vec<Vec<OpKey>> = vec![Vec::new(); terminals.len()];

    for &key in sorted {
        let mut in_count = 0;
        let mut first_owner = 0;
        for (i, reach) in per_terminal.iter().enumerate() {
            if reach.contains(&key) {
                if in_count == 0 {
                    first_owner = i;
                }
                in_count += 1;
            }
        }
        if in_count > 1 || terminals.len() == 1 {
            entry_ops.push(key);
        } else if in_count == 1 {
            case_ops[first_owner].push(key);
        }
    }

    let mut blocks = Vec::new();
    if !entry_ops.is_empty() {
        blocks.push(Block {
            label: "Entry".to_string(),
            ops: entry_ops,
        });
    }
    for (i, case) in case_ops.into_iter().enumerate() {
        if !case.is_empty() {
            blocks.push(Block {
                label: format!("Case({i})"),
                ops: case,
            });
        }
    }
    blocks
}
