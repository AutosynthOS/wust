//! ALU and comparison operation enums.
//!
//! These are shared between the old and new graph IR — they describe
//! the arithmetic/comparison kind, independent of the node model.

/// Arithmetic / logic operation kind.
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

impl AluOp {
    /// Short lowercase name for display.
    pub fn name(&self) -> &'static str {
        match self {
            AluOp::Add => "add",
            AluOp::Sub => "sub",
            AluOp::Mul => "mul",
            AluOp::And => "and",
            AluOp::Or => "or",
            AluOp::Xor => "xor",
            AluOp::Cmp(cmp) => cmp.name(),
        }
    }
}

/// Comparison kind.
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

impl CmpOp {
    /// Short lowercase name for display.
    pub fn name(&self) -> &'static str {
        match self {
            CmpOp::Eq => "cmp_eq",
            CmpOp::Ne => "cmp_ne",
            CmpOp::LtS => "cmp_lts",
            CmpOp::LtU => "cmp_ltu",
            CmpOp::GtS => "cmp_gts",
            CmpOp::GtU => "cmp_gtu",
            CmpOp::LeS => "cmp_les",
            CmpOp::LeU => "cmp_leu",
            CmpOp::GeS => "cmp_ges",
            CmpOp::GeU => "cmp_geu",
        }
    }
}
