pub mod block;
pub mod function;
pub mod instruction;

use crate::backend::PhysReg;

/// A register operand — either already resolved to hardware or virtual (needs regalloc).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Register {
    /// A physical register, already assigned by the backend.
    Phys(u8),
    /// A virtual register, to be resolved by the register allocator.
    Virtual(u32),
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

/// Index into the function builder's vstack table.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VStackId(pub u32);

/// IR-level type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IrType {
    I32,
    I64,
    F32,
    F64,
    V128,
}

/// The source/value of a VStack slot.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Value {
    /// Function parameter at the given index.
    Param(usize),
    /// A constant integer value.
    Const(i64),
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

/// Metadata for a VReg definition.
#[derive(Debug, Clone, Copy)]
pub struct VRegDef {
    pub id: VReg,
    pub ty: IrType,
    pub slot: CanonSlot,
    pub value: Value,
}
