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

use wust_core::{FuncIdx, ValType};

use crate::builder::BlockId;
use crate::op::AluOp;

/// Calling convention / ABI for calls and returns.
/// Determines how inputs/outputs map to physical registers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Abi {
    /// Wasm JIT: position i → PReg(i). inputs[0] → w0, inputs[1] → w1, ...
    WasmJit,
}

new_key_type! {
    /// Key into the VReg arena.
    pub struct VRegKey;
    /// Key into the Operation arena.
    pub struct OpKey;
    /// Key into the VRegRef arena.
    pub struct VRegRefKey;
}

/// A memory slot on the managed stack.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MemSlot {
    pub base: PReg,
    pub offset: u32,
}

impl Ord for MemSlot {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.base
            .0
            .cmp(&other.base.0)
            .then(self.offset.cmp(&other.offset))
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
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VInit {
    pub width: Width,
    pub from_op: Option<OpKey>,
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
    /// Indirect reference to a virtual register or phi node by key.
    VRef(VRegRefKey),
}

impl Into<Input> for VRegKey {
    fn into(self) -> Input {
        Input::VReg(self)
    }
}

impl Into<Input> for VRegRefKey {
    fn into(self) -> Input {
        Input::VRef(self)
    }
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
                VCode::SetSlot(_) | VCode::ClearSlot(_) => {
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
        Input::VRef(..) => unimplemented!(),
    }
}

/// Resolve the vreg referenced by an operation's input at the given index.
pub fn resolve_vreg_input(
    op: &Operation,
    index: usize,
    ops: &slotmap::SlotMap<OpKey, Operation>,
) -> Option<VRegKey> {
    match op.inputs.get(index) {
        Some(Input::VReg(k)) => Some(*k),
        Some(input @ Input::Op(_)) => resolve_input_vreg(input, ops),
        _ => None,
    }
}

/// The opcode of an operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VCode {
    /// Define a value. The VRegDef holds the metadata (const, preg, etc).
    Define,
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
    /// Function call.
    Call {
        func_idx: FuncIdx,
        label: BlockId,
        abi: Abi,
    },
    /// Function return.
    Return { abi: Abi },
    /// Phi — merges two values from if/else branches.
    /// Inputs: [decision (brif), then_value, else_value].
    Phi,
}

impl VCode {
    /// Short name for display purposes.
    pub fn name(&self) -> &'static str {
        match self {
            VCode::Define => "define",
            VCode::Alu(alu) => alu.name(),
            VCode::SetSlot(_) => "set_slot",
            VCode::ClearSlot(_) => "clear_slot",
            VCode::Load(_) => "load",
            VCode::BrIf => "brif",
            VCode::Call { .. } => "call",
            VCode::Return { .. } => "return",
            VCode::Phi => "phi",
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
    pub opcode: VCode,
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

pub fn valtype_width(ty: ValType) -> Width {
    match ty {
        ValType::I32 => Width::W32,
        ValType::I64 => Width::W64,
        ValType::F32 => Width::W32,
        ValType::F64 => Width::W64,
        ty => panic!("unsupported type: {:?}", ty),
    }
}
