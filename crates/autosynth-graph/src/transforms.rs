//! Transforms — fold immediates, mark reachable, sweep dead nodes.
//!
//! These passes simplify the graph before and after the pathfinder:
//! - fold_immediates: replace ALU RHS vreg inputs with Imm12 when the
//!   vreg is a small constant.
//! - mark_reachable: walk operand + effect edges from roots.
//! - sweep: remove dead operations and their vregs.

use std::collections::HashSet;

use autosynth_isa::UImm12;
use slotmap::SlotMap;

use crate::types::{Input, OpCode, OpKey, Operation, VRegDef, VRegKey};

/// For each ALU op with 2 inputs, if the RHS input traces back to a
/// constant vreg with value 0..4095, replace with Input::Imm12.
pub fn fold_immediates(
    sorted: &[OpKey],
    ops: &mut SlotMap<OpKey, Operation>,
    vregs: &SlotMap<VRegKey, VRegDef>,
) {
    for &op_key in sorted {
        let Some(op) = ops.get(op_key) else { continue };
        let is_alu = matches!(op.opcode, OpCode::Alu(_));
        if !is_alu || op.inputs.len() != 2 {
            continue;
        }

        let rhs = &op.inputs[1];
        let val = resolve_const(rhs, ops, vregs);
        let Some(val) = val else { continue };
        if val < 0 || val > 4095 {
            continue;
        }

        let Ok(imm) = UImm12::try_from(val as u16) else {
            continue;
        };
        ops[op_key].inputs[1] = Input::Imm12(imm);
    }
}

/// Resolve an input to a constant value if it references a const vreg.
fn resolve_const(
    input: &Input,
    ops: &SlotMap<OpKey, Operation>,
    vregs: &SlotMap<VRegKey, VRegDef>,
) -> Option<i64> {
    match input {
        Input::Imm12(imm) => Some(imm.value() as i64),
        Input::VReg(key) => vregs.get(*key)?.constant,
        Input::Op(_) => {
            let vreg_key = crate::types::resolve_input_vreg(input, ops)?;
            vregs.get(vreg_key)?.constant
        }
    }
}

/// Walk operand + effect edges from roots, returning all reachable OpKeys.
pub fn mark_reachable(
    roots: &[OpKey],
    ops: &SlotMap<OpKey, Operation>,
    vregs: &SlotMap<VRegKey, VRegDef>,
) -> HashSet<OpKey> {
    let mut live = HashSet::new();

    fn walk(
        key: OpKey,
        ops: &SlotMap<OpKey, Operation>,
        vregs: &SlotMap<VRegKey, VRegDef>,
        live: &mut HashSet<OpKey>,
    ) {
        if !live.insert(key) {
            return;
        }
        let Some(op) = ops.get(key) else { return };
        for input in &op.inputs {
            match input {
                Input::VReg(vreg_key) => {
                    if let Some(def) = vregs.get(*vreg_key) {
                        walk(def.definer, ops, vregs, live);
                    }
                }
                Input::Op(op_key) => {
                    walk(*op_key, ops, vregs, live);
                }
                Input::Imm12(_) => {}
            }
        }
        if let Some(effect) = op.effect {
            walk(effect, ops, vregs, live);
        }
    }

    for &root in roots {
        walk(root, ops, vregs, &mut live);
    }
    live
}

/// Remove dead operations and their vregs from the arenas.
///
/// Returns the filtered sorted list containing only live operations.
pub fn sweep(
    sorted: &[OpKey],
    live: &HashSet<OpKey>,
    ops: &mut SlotMap<OpKey, Operation>,
    vregs: &mut SlotMap<VRegKey, VRegDef>,
) -> Vec<OpKey> {
    let mut result = Vec::new();
    for &key in sorted {
        if live.contains(&key) {
            result.push(key);
        } else {
            // Remove the op's vregs
            if let Some(op) = ops.get(key) {
                let defines: Vec<VRegKey> = op.defines.to_vec();
                for vreg_key in defines {
                    vregs.remove(vreg_key);
                }
            }
            ops.remove(key);
        }
    }
    result
}
