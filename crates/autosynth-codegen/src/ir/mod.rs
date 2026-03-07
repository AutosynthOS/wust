//! Intermediate representation types for the codegen pipeline.
//!
//! The IR is structured as:
//! - [`Register`] — physical or virtual register operand.
//! - [`VReg`] / [`VRegDef`] — virtual registers with type, canonical slot, and value provenance.
//! - [`IrType`] — width-aware IR-level types (i32, i64, f32, f64, v128).
//! - [`Value`] — the source of a virtual register's value (param, constant, another VReg, etc.).
//! - [`CanonSlot`] — the canonical memory location on a virtual stack where a VReg lives.

pub mod block;
pub mod function;
pub mod instruction;

use std::fmt;

use crate::backend::PhysReg;

/// A register operand — either already resolved to hardware or virtual (needs regalloc).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Register {
    /// A physical register, already assigned by the backend.
    Phys(u8),
    /// A virtual register, to be resolved by the register allocator.
    Virtual(u32),
}

impl fmt::Display for Register {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Register::Phys(n) => write!(f, "r{n}"),
            Register::Virtual(n) => write!(f, "v{n}"),
        }
    }
}

impl From<PhysReg> for Register {
    fn from(p: PhysReg) -> Self {
        Register::Phys(p.0)
    }
}

impl From<VReg> for Register {
    fn from(v: VReg) -> Self {
        Register::Virtual(v.0)
    }
}

/// Virtual register — an SSA value with a known type and canonical stack location.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VReg(pub u32);

impl fmt::Display for VReg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "v{}", self.0)
    }
}

/// Index into the function builder's vstack table.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VStackId(pub u32);

/// IR-level value type, determining register width and memory layout.
///
/// Used to select between 32-bit and 64-bit instructions during lowering,
/// and to compute slot sizes in virtual stacks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IrType {
    I32,
    I64,
    F32,
    F64,
    V128,
}

impl fmt::Display for IrType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IrType::I32 => write!(f, "i32"),
            IrType::I64 => write!(f, "i64"),
            IrType::F32 => write!(f, "f32"),
            IrType::F64 => write!(f, "f64"),
            IrType::V128 => write!(f, "v128"),
        }
    }
}

/// The source/value of a VStack slot.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Value {
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
/// Each VReg has a unique id, an IR type that determines its width,
/// an optional canonical stack slot, and a value that describes how
/// it was produced (constant, parameter, ALU result, etc.).
///
/// When `slot` is `None`, the VReg is a **temp** — it has no canonical
/// memory location and cannot be spilled. Temps must be either consumed
/// immediately (e.g. a comparison result feeding the next `BrIf`) or
/// rematerializable from their `value` (e.g. a constant).
#[derive(Debug, Clone, Copy)]
pub struct VRegDef {
    /// The unique virtual register identifier.
    pub id: VReg,
    /// The IR type (determines register width and slot size).
    pub ty: IrType,
    /// Canonical memory location on a virtual stack, or `None` for temps.
    pub slot: Option<CanonSlot>,
    /// How this value was produced.
    pub value: Value,
}
