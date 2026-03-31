use smallvec::SmallVec;
use crate::VRegRef;

/// An operation that produced a value.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Op {
    pub code: OpCode,
    pub uses: SmallVec<[VRegRef; 4]>,
}

/// The operation kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OpCode {
    /// Copy of another value.
    Copy,
    /// ALU operation.
    Add,
    Sub,
    Mul,
    And,
    Or,
    Xor,
    /// Comparison.
    CmpEq,
    CmpNe,
    CmpLtS,
    CmpLtU,
    CmpGtS,
    CmpGtU,
    CmpLeS,
    CmpLeU,
    CmpGeS,
    CmpGeU,
    /// Memory load.
    Load,
    /// Memory store.
    Store,
    /// Set canonical stack slot.
    SetSlot,
    /// Clear canonical stack slot.
    ClearSlot,
    /// Clobber — flush to slot and unbind.
    Clobber,
    /// Materialize — ensure value is in a register.
    Materialize,
    /// Phi — merge point from multiple predecessors.
    Phi,
    /// Branch-and-link (function call).
    Call,
    /// Conditional branch.
    BrIf,
    /// Unconditional branch.
    Branch,
    /// Return.
    Return,
}
