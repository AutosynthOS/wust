use crate::node::NodeRef;
use autosynth_isa::{PReg, UImm12};
use smallvec::SmallVec;

/// A typed operand — either a vreg reference or a folded immediate.
///
/// When folded to an immediate, the original NodeRef chain is dropped.
/// No dead traversal — the Rc dies, the chain is gone.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Operand {
    VReg(NodeRef),
    UImm12(UImm12),
}

impl Operand {
    /// Get the NodeRef if this is a VReg operand.
    pub fn as_vreg(&self) -> Option<&NodeRef> {
        match self {
            Operand::VReg(r) => Some(r),
            _ => None,
        }
    }
}

/// An operation that produced a value.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Op {
    pub code: VCode,
    pub uses: SmallVec<[Operand; 4]>,
    /// Previous side effect (ordering constraint).
    pub effect: Option<NodeRef>,
}

impl Op {
    /// Map over all child NodeRefs (VReg operands + effect).
    /// UImm12 operands are left untouched — no NodeRef to traverse.
    pub fn map_refs(&self, mut f: impl FnMut(&NodeRef) -> NodeRef) -> Op {
        Op {
            code: self.code,
            uses: self.uses.iter().map(|u| match u {
                Operand::VReg(r) => Operand::VReg(f(r)),
                Operand::UImm12(imm) => Operand::UImm12(*imm),
            }).collect(),
            effect: self.effect.as_ref().map(&mut f),
        }
    }
}

/// The operation kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VCode {
    Alu(AluOp),
    /// Extract a return value from a call. PReg on the VRegState
    /// indicates which result register (w0, w1, ...).
    UseCallResult,
    Load,
    Store,
    SetSlot,
    ClearSlot,
    Clobber,
    Materialize,
    /// Set target PReg constraint on a value.
    SetTarget(PReg),
    Phi,
    Call(u32),
    BrIf,
    Branch,
    Return,
    /// Values that need to survive across a call.
    /// Operands: the needed values. Effect: the call.
    Needs,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AluOp {
    Add,
    Sub,
    Mul,
    And,
    Or,
    Xor,
    Cmp(CmpOp),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CmpOp {
    Eq,
    Ne,
    LtS,
    LtU,
    GtS,
    GtU,
    LeS,
    LeU,
    GeS,
    GeU,
}
