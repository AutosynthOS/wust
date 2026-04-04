//! Wasm-to-graph compiler with faithful operand stack modeling.
//!
//! Walks a `FuncMeta`'s bytecodes and produces the graph IR:
//! `SlotMap<OpKey, Operation>`, `SlotMap<VRegKey, VRegDef>`, and root
//! `OpKey`s for block detection and scheduling.
//!
//! The builder tracks wasm-level state via two regions:
//! - **Locals**: params + declared locals, indexed by local number.
//! - **Operands**: the wasm operand stack, push/pop by bytecode flow.
//!
//! Every operand stack push emits a `SetSlot` and every pop emits a
//! `ClearSlot`. These operations use `Input::Op` for ordering (oref)
//! and `Input::VReg` for data (vref), matching the TS prototype
//! pattern exactly. ALU ops reference the `ClearSlot` pop operations
//! via `Input::Op`, and the underlying vreg is derived by tracing
//! through the op reference chain.

use autosynth_isa::{PReg, Width};
use slotmap::SlotMap;
use smallvec::smallvec;
use wust_core::{FRAME_HEADER_SIZE, FuncMeta, OpCode as WasmOp};

use crate::op::{AluOp, CmpOp};
use crate::types::{Input, MemSlot, OpCode, OpKey, Operation, VRegDef, VRegKey};

/// ABI registers.
const G_LB: PReg = PReg(29);

/// An entry in a region: tracks both the vreg and the last operation
/// that touched this slot (for ordering chains).
#[derive(Clone)]
struct RegionEntry {
    vreg: VRegKey,
    last_op: OpKey,
}

/// A contiguous region on the managed stack.
///
/// Tracks which VRegKey occupies each slot, along with the OpKey of
/// the last operation that touched it (for ordering via `Input::Op`).
/// The `base` and `base_offset` determine the MemSlot address for
/// SetSlot/ClearSlot/Load operations.
#[derive(Clone)]
struct Region {
    base: PReg,
    base_offset: u16,
    cursor: u16,
    entries: Vec<RegionEntry>,
}

impl Region {
    fn new(base: PReg, base_offset: u16) -> Self {
        Self {
            base,
            base_offset,
            cursor: 0,
            entries: Vec::new(),
        }
    }

    /// Record a vreg in the region without emitting any operation.
    ///
    /// Used for initial param/local setup where the value definition
    /// is the Param/Const op itself, not a SetSlot.
    fn define(&mut self, vreg: VRegKey, defining_op: OpKey) {
        self.entries.push(RegionEntry {
            vreg,
            last_op: defining_op,
        });
        self.cursor += 4; // W32 = 4 bytes
    }

    /// Push a vreg onto this region, returning the MemSlot it occupies.
    ///
    /// Advances the cursor by 4 bytes (W32). The caller is responsible
    /// for emitting the SetSlot operation and updating `last_op`.
    fn push(&mut self, vreg: VRegKey, last_op: OpKey) -> MemSlot {
        let slot = self.mem_slot_at_cursor();
        self.entries.push(RegionEntry { vreg, last_op });
        self.cursor += 4;
        slot
    }

    /// Pop a vreg from this region, returning the entry and its MemSlot.
    ///
    /// Decrements the cursor by 4 bytes. The caller is responsible for
    /// emitting the ClearSlot operation.
    fn pop(&mut self) -> (RegionEntry, MemSlot) {
        let entry = self.entries.pop().expect("region underflow");
        self.cursor -= 4;
        let slot = self.mem_slot_at_cursor();
        (entry, slot)
    }

    /// Get the entry at the given index.
    fn get(&self, idx: usize) -> &RegionEntry {
        &self.entries[idx]
    }

    /// Set the vreg at the given index.
    fn set(&mut self, idx: usize, vreg: VRegKey, last_op: OpKey) {
        self.entries[idx] = RegionEntry { vreg, last_op };
    }

    /// Compute the MemSlot for entry at the given index.
    fn mem_slot(&self, idx: usize) -> MemSlot {
        MemSlot {
            base: self.base,
            offset: self.base_offset as u32 + (idx as u32 * 4),
        }
    }

    /// Compute the MemSlot at the current cursor position.
    fn mem_slot_at_cursor(&self) -> MemSlot {
        MemSlot {
            base: self.base,
            offset: self.base_offset as u32 + self.cursor as u32,
        }
    }
}

/// Per-block wasm state: locals region, operand stack, effect chain.
///
/// Cloning snapshots the state for branching (if/else/end).
#[derive(Clone)]
struct WasmBlock {
    locals: Region,
    operands: Region,
    /// Most recent side-effecting operation in this block.
    last_effect: Option<OpKey>,
}

/// Output of the wasm-to-graph compiler.
pub struct WasmGraph {
    pub ops: SlotMap<OpKey, Operation>,
    pub vregs: SlotMap<VRegKey, VRegDef>,
    pub roots: Vec<OpKey>,
}

/// Push a vreg onto the operand stack, emitting a SetSlot operation.
///
/// The SetSlot takes two inputs matching the TS prototype pattern:
/// - `Input::Op(ordering_op)` — ordering dependency (oref)
/// - `Input::VReg(vreg)` — the value being stored (vref)
///
/// Returns the OpKey of the SetSlot for chaining.
fn operand_push(
    vreg: VRegKey,
    ordering_op: OpKey,
    block: &mut WasmBlock,
    ops: &mut SlotMap<OpKey, Operation>,
) -> OpKey {
    let slot = block.operands.push(vreg, OpKey::default());
    let set_key = ops.insert_with_key(|_| Operation {
        opcode: OpCode::SetSlot(slot),
        inputs: smallvec![Input::Op(ordering_op), Input::VReg(vreg)],
        effect: None,
        prev: None,
        defines: smallvec![],
    });
    // Update the entry's last_op to point to this SetSlot.
    let last_idx = block.operands.entries.len() - 1;
    block.operands.entries[last_idx].last_op = set_key;
    set_key
}

/// Pop a vreg from the operand stack, emitting a ClearSlot operation.
///
/// The ClearSlot takes two inputs matching the TS prototype pattern:
/// - `Input::Op(set_slot_key)` — ordering dependency on the push (oref)
/// - `Input::VReg(vreg)` — the value being cleared (vref)
///
/// Returns the OpKey of the ClearSlot. ALU operations should reference
/// this ClearSlot via `Input::Op` to establish ordering and derive
/// the underlying vreg.
fn operand_pop(
    block: &mut WasmBlock,
    ops: &mut SlotMap<OpKey, Operation>,
) -> OpKey {
    let (entry, slot) = block.operands.pop();
    let clear_key = ops.insert_with_key(|_| Operation {
        opcode: OpCode::ClearSlot(slot),
        inputs: smallvec![Input::Op(entry.last_op), Input::VReg(entry.vreg)],
        effect: None,
        prev: None,
        defines: smallvec![],
    });
    clear_key
}

/// Compile a wasm function to the graph IR.
///
/// Walks the bytecodes in `func.body.ops`, translating each wasm
/// instruction to operations and vregs. `funcs` provides signatures
/// for call target resolution.
///
/// # Algorithm
///
/// 1. Initialize locals region with param ops (preg-hinted) and
///    declared-local const-zero ops. SetSlot emitted for each to
///    establish the local's memory position.
/// 2. Walk each bytecode:
///    - Arithmetic/comparison: pop operands (ClearSlot each via oref),
///      create ALU op with Input::Op refs to the ClearSlots, push
///      result (SetSlot).
///    - LocalGet: push local's vreg to operand stack (SetSlot with
///      oref to last op touching that local).
///    - LocalSet: pop from operand stack (ClearSlot), emit SetSlot
///      to local's memory position.
///    - I32Const: create Const op, push to operand stack (SetSlot).
///    - If: pop condition (ClearSlot), create BrIf with oref to pop.
///    - Else: swap saved and current block states.
///    - End: merge blocks, creating phi nodes where values diverge.
///    - Call: pop args (ClearSlot each), create Call with oref to
///      pops, push result (SetSlot).
///    - Return: pop results (ClearSlot each), create Return with
///      oref to pops.
/// 3. If the operand stack is non-empty at function end, emit an
///    implicit return for the remaining values.
/// 4. Return (ops, vregs, roots).
pub fn compile(func: &FuncMeta, funcs: &[FuncMeta]) -> WasmGraph {
    let mut ops: SlotMap<OpKey, Operation> = SlotMap::with_key();
    let mut vregs: SlotMap<VRegKey, VRegDef> = SlotMap::with_key();

    let locals_size = func.locals_size;
    let operand_base = locals_size as u16 + FRAME_HEADER_SIZE as u16;

    let mut block = WasmBlock {
        locals: Region::new(G_LB, 0),
        operands: Region::new(G_LB, operand_base),
        last_effect: None,
    };

    // Define params — each arrives in a PReg per calling convention.
    // Emit a SetSlot for each param to establish its local memory
    // position, matching the TS prototype pattern.
    for (i, _ty) in func.params.iter().enumerate() {
        let op_key = ops.insert_with_key(|_| Operation {
            opcode: OpCode::Param,
            inputs: smallvec![],
            effect: None,
            prev: None,
            defines: smallvec![],
        });
        let vreg = vregs.insert(VRegDef {
            width: Width::W32,
            definer: op_key,
            constant: None,
            preg: Some(PReg(i as u8)),
            mem: None,
        });
        ops[op_key].defines = smallvec![vreg];

        // SetSlot to local memory — NOT in the effect chain.
        // Ordering comes from the oref to the param op.
        let mem = block.locals.mem_slot(i);
        let set_key = ops.insert_with_key(|_| Operation {
            opcode: OpCode::SetSlot(mem),
            inputs: smallvec![Input::Op(op_key), Input::VReg(vreg)],
            effect: None,
            prev: None,
            defines: smallvec![],
        });
        block.locals.define(vreg, set_key);
    }

    // Define declared locals — const 0.
    for (_i, _ty) in func.locals.iter().enumerate() {
        let op_key = ops.insert_with_key(|_| Operation {
            opcode: OpCode::Const,
            inputs: smallvec![],
            effect: None,
            prev: None,
            defines: smallvec![],
        });
        let vreg = vregs.insert(VRegDef {
            width: Width::W32,
            definer: op_key,
            constant: Some(0),
            preg: None,
            mem: None,
        });
        ops[op_key].defines = smallvec![vreg];
        block.locals.define(vreg, op_key);
    }

    let mut roots: Vec<OpKey> = Vec::new();

    // Block nesting stack: (brif_key, saved_block, has_else).
    let mut nesting: Vec<(OpKey, WasmBlock, bool)> = Vec::new();

    let mut pc = 0;
    loop {
        let inline_op = &func.body.ops[pc];
        let wasm_op = inline_op.opcode();

        match wasm_op {
            WasmOp::I32Const => {
                let val = inline_op.immediate_i32() as i64;
                let op_key = ops.insert_with_key(|_| Operation {
                    opcode: OpCode::Const,
                    inputs: smallvec![],
                    effect: None,
                    prev: None,
                    defines: smallvec![],
                });
                let vreg = vregs.insert(VRegDef {
                    width: Width::W32,
                    definer: op_key,
                    constant: Some(val),
                    preg: None,
                    mem: None,
                });
                ops[op_key].defines = smallvec![vreg];
                operand_push(vreg, op_key, &mut block, &mut ops);
            }

            WasmOp::LocalGetI32 => {
                let idx = inline_op.local_index() as usize;
                let entry = block.locals.get(idx).clone();
                operand_push(entry.vreg, entry.last_op, &mut block, &mut ops);
            }

            WasmOp::LocalSetI32 => {
                let idx = inline_op.local_index() as usize;
                let pop_key = operand_pop(&mut block, &mut ops);
                let vreg = crate::types::resolve_input_vreg(
                    &Input::Op(pop_key),
                    &ops,
                ).expect("pop should resolve to a vreg");
                let mem = block.locals.mem_slot(idx);

                // Emit SetSlot to write the value to the local's
                // memory position. NOT in the effect chain — ordering
                // comes from the Input::Op chain. Effect chain is
                // reserved for control flow (brif, call, return).
                let set_key = ops.insert_with_key(|_| Operation {
                    opcode: OpCode::SetSlot(mem),
                    inputs: smallvec![Input::Op(pop_key), Input::VReg(vreg)],
                    effect: None,
                    prev: None,
                    defines: smallvec![],
                });
                block.locals.set(idx, vreg, set_key);
            }

            WasmOp::I32Add => {
                emit_binary(AluOp::Add, &mut block, &mut ops, &mut vregs);
            }
            WasmOp::I32Sub => {
                emit_binary(AluOp::Sub, &mut block, &mut ops, &mut vregs);
            }
            WasmOp::I32Mul => {
                emit_binary(AluOp::Mul, &mut block, &mut ops, &mut vregs);
            }

            WasmOp::I32LeS => {
                emit_binary(
                    AluOp::Cmp(CmpOp::LeS),
                    &mut block,
                    &mut ops,
                    &mut vregs,
                );
            }
            WasmOp::I32Eqz => {
                let pop_key = operand_pop(&mut block, &mut ops);

                let zero_key = ops.insert_with_key(|_| Operation {
                    opcode: OpCode::Const,
                    inputs: smallvec![],
                    effect: None,
                    prev: None,
                    defines: smallvec![],
                });
                let zero = vregs.insert(VRegDef {
                    width: Width::W32,
                    definer: zero_key,
                    constant: Some(0),
                    preg: None,
                    mem: None,
                });
                ops[zero_key].defines = smallvec![zero];

                let cmp_key = ops.insert_with_key(|_| Operation {
                    opcode: OpCode::Alu(AluOp::Cmp(CmpOp::Eq)),
                    inputs: smallvec![Input::Op(pop_key), Input::VReg(zero)],
                    effect: None,
                    prev: None,
                    defines: smallvec![],
                });
                let result = vregs.insert(VRegDef {
                    width: Width::W32,
                    definer: cmp_key,
                    constant: None,
                    preg: None,
                    mem: None,
                });
                ops[cmp_key].defines = smallvec![result];
                operand_push(result, cmp_key, &mut block, &mut ops);
            }

            WasmOp::Return => {
                let mut inputs = smallvec::SmallVec::<[Input; 2]>::new();
                for _i in 0..func.results.len() {
                    let pop_key = operand_pop(&mut block, &mut ops);
                    inputs.push(Input::Op(pop_key));
                }
                // Reverse so result 0 is first in the inputs list.
                inputs.reverse();

                let ret_key = ops.insert_with_key(|_| Operation {
                    opcode: OpCode::Return,
                    inputs,
                    effect: block.last_effect,
                    prev: None,
                    defines: smallvec![],
                });
                block.last_effect = Some(ret_key);
                roots.push(ret_key);
            }

            WasmOp::Call => {
                let callee_idx = inline_op.immediate_u32();
                let callee = &funcs[callee_idx as usize];

                // Pop arguments (rightmost first from stack).
                let mut arg_pop_keys = Vec::new();
                for _ in 0..callee.params.len() {
                    arg_pop_keys.push(operand_pop(&mut block, &mut ops));
                }
                arg_pop_keys.reverse();
                let mut args = smallvec::SmallVec::<[Input; 2]>::new();
                for &pop_key in &arg_pop_keys {
                    args.push(Input::Op(pop_key));
                }

                let call_key = ops.insert_with_key(|_| Operation {
                    opcode: OpCode::Call(callee_idx),
                    inputs: args,
                    effect: block.last_effect,
                    prev: None,
                    defines: smallvec![],
                });

                // Call result — arrives in w0 (ABI-fixed).
                let result = vregs.insert(VRegDef {
                    width: Width::W32,
                    definer: call_key,
                    constant: None,
                    preg: Some(PReg(0)),
                    mem: None,
                });
                ops[call_key].defines = smallvec![result];
                block.last_effect = Some(call_key);

                // Push return values onto the operand stack.
                if !callee.results.is_empty() {
                    operand_push(result, call_key, &mut block, &mut ops);
                }
            }

            WasmOp::If => {
                let pop_key = operand_pop(&mut block, &mut ops);
                let brif_key = ops.insert_with_key(|_| Operation {
                    opcode: OpCode::BrIf,
                    inputs: smallvec![Input::Op(pop_key)],
                    effect: block.last_effect,
                    prev: None,
                    defines: smallvec![],
                });
                block.last_effect = Some(brif_key);

                // Save the pre-if state for the else/continuation path.
                let entry_block = block.clone();
                nesting.push((brif_key, entry_block, false));
            }

            WasmOp::Else => {
                let (_, entry_block, has_else) =
                    nesting.last_mut().expect("Else without If");
                *has_else = true;
                // Swap: save the then-path state, restore entry state
                // for else.
                let then_block =
                    std::mem::replace(&mut block, entry_block.clone());
                *entry_block = then_block;
            }

            WasmOp::End => {
                let block_idx = inline_op.immediate_u32();
                // block_idx 0 = function-level end.
                if block_idx == 0 {
                    break;
                }

                let (_brif_key, saved_block, has_else) =
                    nesting.pop().expect("End without If");

                if has_else {
                    // saved_block = then-path (swapped at Else).
                    // block = else-path.
                    let else_block = block.clone();
                    let then_block = saved_block;
                    merge_blocks(
                        &mut block,
                        &then_block,
                        &else_block,
                        _brif_key,
                        &mut ops,
                        &mut vregs,
                    );
                } else {
                    // No else — the then-path may have terminated
                    // (return). Restore entry state for continuation.
                    block = saved_block;
                }
            }

            _ => {
                // Skip structural ops that don't produce graph nodes.
            }
        }

        pc += 1;
    }

    // Implicit return: if the operand stack has values at function
    // end, emit a return node for them.
    if !block.operands.entries.is_empty() {
        let mut inputs = smallvec::SmallVec::<[Input; 2]>::new();
        for entry in &block.operands.entries {
            inputs.push(Input::Op(entry.last_op));
        }
        let ret_key = ops.insert_with_key(|_| Operation {
            opcode: OpCode::Return,
            inputs,
            effect: block.last_effect,
            prev: None,
            defines: smallvec![],
        });
        roots.push(ret_key);
    }

    WasmGraph { ops, vregs, roots }
}

/// Spill all locals whose vreg has a preg and isn't a constant.
///
/// Emits a SetSlot for each such local to back the register value
/// with a memory copy. Chains each SetSlot into the effect chain.
/// Skips locals that are already constant (no clobber concern).
fn spill_live_locals(
    locals: &Region,
    last_effect: &mut Option<OpKey>,
    ops: &mut SlotMap<OpKey, Operation>,
    vregs: &SlotMap<VRegKey, VRegDef>,
) {
    for (idx, entry) in locals.entries.iter().enumerate() {
        let Some(def) = vregs.get(entry.vreg) else {
            continue;
        };
        // Skip constants — they don't need memory backing.
        if def.constant.is_some() {
            continue;
        }
        // Skip vregs without a preg — they're already in vreg-space
        // and the pathfinder will handle them.
        if def.preg.is_none() {
            continue;
        }
        let mem = locals.mem_slot(idx);
        let set_key = ops.insert_with_key(|_| Operation {
            opcode: OpCode::SetSlot(mem),
            inputs: smallvec![Input::Op(entry.last_op), Input::VReg(entry.vreg)],
            effect: *last_effect,
            prev: None,
            defines: smallvec![],
        });
        *last_effect = Some(set_key);
    }
}

/// Emit a binary ALU operation.
///
/// Pops two operands (emitting ClearSlot for each), creates the ALU
/// op with `Input::Op` refs to the ClearSlots, and pushes the result
/// (emitting SetSlot).
fn emit_binary(
    alu: AluOp,
    block: &mut WasmBlock,
    ops: &mut SlotMap<OpKey, Operation>,
    vregs: &mut SlotMap<VRegKey, VRegDef>,
) {
    let rhs_pop = operand_pop(block, ops);
    let lhs_pop = operand_pop(block, ops);

    let op_key = ops.insert_with_key(|_| Operation {
        opcode: OpCode::Alu(alu),
        inputs: smallvec![Input::Op(lhs_pop), Input::Op(rhs_pop)],
        effect: None,
        prev: None,
        defines: smallvec![],
    });
    let result = vregs.insert(VRegDef {
        width: Width::W32,
        definer: op_key,
        constant: None,
        preg: None,
        mem: None,
    });
    ops[op_key].defines = smallvec![result];
    operand_push(result, op_key, block, ops);
}

/// Merge two divergent block states, creating phi nodes where values
/// differ.
///
/// After an if/else, the then-path and else-path may have different
/// VRegKeys in the same locals/operands positions. For each
/// divergence, a Phi operation is created that selects between the
/// two values based on the BrIf decision.
fn merge_blocks(
    output: &mut WasmBlock,
    then_block: &WasmBlock,
    else_block: &WasmBlock,
    decision: OpKey,
    ops: &mut SlotMap<OpKey, Operation>,
    vregs: &mut SlotMap<VRegKey, VRegDef>,
) {
    // Start from the else block as a base, then merge.
    *output = else_block.clone();

    merge_region_entries(
        &mut output.locals.entries,
        &then_block.locals.entries,
        &else_block.locals.entries,
        decision,
        ops,
        vregs,
    );
    merge_region_entries(
        &mut output.operands.entries,
        &then_block.operands.entries,
        &else_block.operands.entries,
        decision,
        ops,
        vregs,
    );
}

/// Merge region entries, creating phi ops where then != else.
fn merge_region_entries(
    target: &mut [RegionEntry],
    then_entries: &[RegionEntry],
    else_entries: &[RegionEntry],
    _decision: OpKey,
    ops: &mut SlotMap<OpKey, Operation>,
    vregs: &mut SlotMap<VRegKey, VRegDef>,
) {
    assert_eq!(then_entries.len(), else_entries.len());
    for i in 0..then_entries.len() {
        if then_entries[i].vreg != else_entries[i].vreg {
            // TODO: use a proper Phi opcode instead of ALU Add
            // placeholder.
            let phi_key = ops.insert_with_key(|_| Operation {
                opcode: OpCode::Alu(AluOp::Add),
                inputs: smallvec![
                    Input::VReg(then_entries[i].vreg),
                    Input::VReg(else_entries[i].vreg),
                ],
                effect: None,
                prev: None,
                defines: smallvec![],
            });
            let phi_vreg = vregs.insert(VRegDef {
                width: Width::W32,
                definer: phi_key,
                constant: None,
                preg: None,
                mem: None,
            });
            ops[phi_key].defines = smallvec![phi_vreg];
            target[i] = RegionEntry {
                vreg: phi_vreg,
                last_op: phi_key,
            };
        }
    }
}
