//! Intermediate representation types for the codegen pipeline.
//!
//! Core instruction types (`IrInst`, `AluOp`, `Operand`, `Register`, `VReg`,
//! `BlockId`, `FunctionIdx`) are re-exported from [`autosynth_ir`].
//!
//! Types specific to this crate's codegen pipeline (`VRegDef`, `CanonSlot`,
//! `Value`, `VStackId`, `VStackMut`) are defined here.

pub mod block;
pub mod function;
pub mod instruction;

use std::fmt;

use autosynth_isa::Width;

// Re-export core IR types from autosynth-ir.
pub use autosynth_ir::{AluOp, BlockId, FunctionIdx, Operand, Register, VReg};

/// Index into the function builder's vstack table.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VStackId(pub u32);

/// Mutable vstack state — depth and slot assignments.
///
/// This is the per-block part of a vstack. It gets cloned at block
/// boundaries (branches snapshot it onto target blocks).
#[derive(Debug, Clone)]
pub struct VStackMut {
    /// Current stack depth (number of occupied slots).
    pub depth: u32,
    /// Slot assignments (index → VReg).
    pub slots: Vec<Option<VReg>>,
}

/// The source/value of a VStack slot.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Value {
    /// An instruction destination — value comes from the instruction
    /// that writes to this VReg (e.g. ALU result, call return).
    Destination,
    /// Function parameter at the given index.
    Param(usize),
    /// A constant integer value.
    ConstI64(i64),
    /// A constant i32 value.
    ConstI32(i32),
    /// The value of another VReg.
    VReg(VReg),
    /// The current value of a register (physical or virtual).
    Reg(Register),
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Destination => write!(f, "dst"),
            Value::Param(i) => write!(f, "param({i})"),
            Value::ConstI64(n) => write!(f, "#{n}"),
            Value::ConstI32(n) => write!(f, "#{n}"),
            Value::VReg(v) => write!(f, "{v}"),
            Value::Reg(r) => write!(f, "{r}"),
        }
    }
}

/// Canonical memory location for a VReg — where it lives on the stack.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CanonSlot {
    /// Which virtual stack this slot belongs to.
    pub vstack: VStackId,
    /// Slot index within that vstack.
    pub index: u32,
    /// Byte offset from the vstack's base (base_reg + base_offset + slot_offset).
    pub byte_offset: u32,
    /// Size in bytes (4 for i32/f32, 8 for i64/f64, 16 for v128).
    pub size: u8,
}

/// Metadata for a virtual register definition.
///
/// Each VReg has a unique id, a width that determines register size and
/// memory layout, an optional canonical stack slot, and a value that
/// describes how it was produced (constant, parameter, ALU result, etc.).
///
/// When `slot` is `None`, the VReg is a **temp** — it has no canonical
/// memory location and cannot be spilled. Temps must be either consumed
/// immediately (e.g. a comparison result feeding the next `BrIf`) or
/// rematerializable from their `value` (e.g. a constant).
#[derive(Debug, Clone, Copy)]
pub struct VRegDef {
    /// The unique virtual register identifier.
    pub id: VReg,
    /// Register width (W32 or W64) — determines instruction width and slot size.
    pub width: Width,
    /// Canonical memory location on a virtual stack, or `None` for temps.
    pub slot: Option<CanonSlot>,
    /// How this value was produced.
    pub value: Value,
    /// Whether this value can be cheaply recomputed (e.g. `movz` for constants)
    /// instead of spilled to memory. Rematerializable values can be evicted
    /// without a store and re-emitted on next use.
    pub remat: bool,
}
