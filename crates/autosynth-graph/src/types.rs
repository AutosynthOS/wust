//! Core types for the grid-based register allocator.
//!
//! Operations and VRegs live in separate SlotMap arenas, referenced by
//! typed keys. The grid (slot state) is a BTreeMap<SlotKey, VRegKey>
//! that tracks which vreg lives in which physical location at each
//! point in the program.

use std::fmt;

use autosynth_isa::{PReg, UImm12, Width};
use slotmap::new_key_type;
use smallvec::SmallVec;

use crate::op::AluOp;

new_key_type! {
    /// Key into the VReg arena.
    pub struct VRegKey;
    /// Key into the Operation arena.
    pub struct OpKey;
}

/// A memory slot on the managed stack.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MemSlot {
    pub base: PReg,
    pub offset: u32,
}

impl Ord for MemSlot {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.base.0.cmp(&other.base.0).then(self.offset.cmp(&other.offset))
    }
}

impl PartialOrd for MemSlot {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Display for MemSlot {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[x{}+{}]", self.base.0, self.offset)
    }
}

/// Metadata for a virtual register.
///
/// The vreg knows which operation defined it, its width, and optional
/// hints for where it should live (preg, memory slot, constant).
#[derive(Debug, Clone)]
pub struct VRegDef {
    pub width: Width,
    pub definer: OpKey,
    pub constant: Option<i64>,
    pub preg: Option<PReg>,
    pub mem: Option<MemSlot>,
}

/// An input operand to an operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Input {
    /// Reference to a virtual register.
    VReg(VRegKey),
    /// Reference to another operation (for ordering + derived vreg).
    ///
    /// Used by set_slot/clear_slot (ordering chain) and ALU ops
    /// (referencing clear_slot pops). The vreg is resolved by tracing
    /// through the referenced operation's defines or vref operands.
    Op(OpKey),
    /// A folded 12-bit unsigned immediate.
    Imm12(UImm12),
}

/// Resolve an input to the VRegKey it references.
///
/// Mirrors the TS prototype's `resolveOperandVreg`:
/// - `VReg(k)` → Some(k)
/// - `Imm12(_)` → None
/// - `Op(key)` → look up the operation:
///   - If it defines a vreg, return that vreg
///   - If it's a set_slot/clear_slot, check operands[1] (vref) or
///     recursively resolve operands[0] (oref chain)
pub fn resolve_input_vreg(
    input: &Input,
    ops: &slotmap::SlotMap<OpKey, Operation>,
) -> Option<VRegKey> {
    match input {
        Input::VReg(k) => Some(*k),
        Input::Imm12(_) => None,
        Input::Op(op_key) => {
            let op = ops.get(*op_key)?;
            // If the op defines a vreg, return it.
            if let Some(&vreg) = op.defines.first() {
                return Some(vreg);
            }
            // For set_slot/clear_slot: check the vref operand (index 1),
            // then fall back to recursively resolving the oref (index 0).
            match op.opcode {
                OpCode::SetSlot(_) | OpCode::ClearSlot(_) => {
                    if let Some(Input::VReg(k)) = op.inputs.get(1) {
                        return Some(*k);
                    }
                    if let Some(oref) = op.inputs.first() {
                        return resolve_input_vreg(oref, ops);
                    }
                    None
                }
                _ => None,
            }
        }
    }
}

/// The opcode of an operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpCode {
    /// Function parameter — defines a vreg arriving in a PReg.
    Param,
    /// Constant materialization.
    Const,
    /// ALU operation (add, sub, cmp, etc.).
    Alu(AluOp),
    /// Store a vreg to a memory slot (spill).
    SetSlot(MemSlot),
    /// Remove a memory slot entry.
    ClearSlot(MemSlot),
    /// Load a vreg from a memory slot (reload).
    Load(MemSlot),
    /// Conditional branch.
    BrIf,
    /// Function call to callee at the given function index.
    Call(u32),
    /// Function return.
    Return,
}

impl OpCode {
    /// Short name for display purposes.
    pub fn name(&self) -> &'static str {
        match self {
            OpCode::Param => "param",
            OpCode::Const => "const",
            OpCode::Alu(alu) => alu.name(),
            OpCode::SetSlot(_) => "set_slot",
            OpCode::ClearSlot(_) => "clear_slot",
            OpCode::Load(_) => "load",
            OpCode::BrIf => "brif",
            OpCode::Call(_) => "call",
            OpCode::Return => "return",
        }
    }
}

/// An operation in the graph.
///
/// Stored in `SlotMap<OpKey, Operation>`. Inputs reference VRegKeys
/// or immediates. Effect chains link side-effecting operations.
/// The `prev` pointer is set by topological sort — it points to
/// the immediately preceding operation in the total order.
#[derive(Debug, Clone)]
pub struct Operation {
    pub opcode: OpCode,
    pub inputs: SmallVec<[Input; 2]>,
    /// Previous side-effecting operation (declared dependency).
    pub effect: Option<OpKey>,
    /// Previous operation in the topological order (set by topo sort).
    pub prev: Option<OpKey>,
    /// VRegs defined by this operation.
    pub defines: SmallVec<[VRegKey; 1]>,
}

/// Identifies a slot in the grid state.
///
/// The grid maps SlotKeys to VRegKeys — "which vreg is in this location?"
/// Ordered by Ord for deterministic BTreeMap iteration.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SlotKey {
    /// Physical register slot.
    PReg(PReg),
    /// Memory slot on the managed stack.
    Mem(MemSlot),
    /// Constant value.
    Const(i64),
    /// Unassigned vreg (in "vreg space" — needs a real slot).
    VReg(VRegKey),
}

/// Manual Ord implementation for deterministic iteration.
///
/// Order: PReg (by number) < Mem (by base, then offset) < Const (by value) < VReg (by key).
impl Ord for SlotKey {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use SlotKey::*;
        match (self, other) {
            (PReg(a), PReg(b)) => a.0.cmp(&b.0),
            (PReg(_), _) => std::cmp::Ordering::Less,
            (_, PReg(_)) => std::cmp::Ordering::Greater,

            (Mem(a), Mem(b)) => a.cmp(b),
            (Mem(_), _) => std::cmp::Ordering::Less,
            (_, Mem(_)) => std::cmp::Ordering::Greater,

            (Const(a), Const(b)) => a.cmp(b),
            (Const(_), _) => std::cmp::Ordering::Less,
            (_, Const(_)) => std::cmp::Ordering::Greater,

            (VReg(a), VReg(b)) => a.cmp(b),
        }
    }
}

impl PartialOrd for SlotKey {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
