//! Function-level IR types: function indices, ISA register roles, virtual
//! stack definitions, and the finalized [`IRFunction`].

use super::block::IrBlock;
use super::{Register, VReg, VRegDef, VStackId};

/// Index identifying a function in the compilation unit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FunctionIdx {
    /// A user-defined function, indexed by its position in the module.
    User(u32),
}

/// Architecture-abstract register role, resolved to a physical register by
/// the backend via [`BackendEmitter::use_isa_reg`](crate::backend::BackendEmitter::use_isa_reg).
///
/// The caller uses this to declare named registers with specific architectural
/// roles without knowing the target platform's register numbering.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IsaReg {
    /// The platform's frame pointer register (e.g. x29 on aarch64).
    FramePointer,
    /// The platform's stack pointer register (e.g. x28 as software SP on aarch64).
    StackPointer,
    /// The platform's return address / link register (e.g. x30 on aarch64).
    ReturnAddress,
    /// A general-purpose 64-bit register, auto-allocated from the remaining pool.
    /// Positive indexes allocate from the start (0, 1, 2...),
    /// negative indexes allocate from the end (-1, -2, -3...).
    Define64(i8),
}

/// Definition of a virtual stack — anchored to a register + offset.
#[derive(Debug)]
pub struct VStackDef {
    pub id: VStackId,
    /// The register this stack is relative to (always Phys in practice).
    pub base: Register,
    /// Byte offset from the base register to the start of this stack.
    pub base_offset: u32,
    /// Final stack depth (number of slots).
    pub depth: u32,
    /// Slot definitions (index → VReg).
    pub slots: Vec<Option<VReg>>,
}

/// A complete IR function — the finalized output of FunctionBuilder.
///
/// This is a read-only type. All mutation happens during building.
/// Blocks have their params, results, and successors computed.
#[derive(Debug)]
pub struct IRFunction {
    /// All virtual stacks defined for this function.
    pub vstacks: Vec<VStackDef>,
    /// All VReg definitions, indexed by VReg id.
    pub vreg_defs: Vec<VRegDef>,
    /// All blocks with analyzed control flow.
    pub blocks: Vec<IrBlock>,
}
