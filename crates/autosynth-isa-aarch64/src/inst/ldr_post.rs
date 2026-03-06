use crate::imm::SImm9;
use crate::reg::{GprOrZr, GprOrSp};

use super::Aarch64Inst;

/// `LDR Rt, [Rn], #simm9` — load with post-index.
///
/// After the load, Rn is incremented by the signed immediate.
/// Width is derived from `rt`. `Rn` is always a 64-bit base.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LdrPost {
    pub rt: GprOrZr,
    pub rn: GprOrSp,
    pub imm: SImm9,
}

impl Aarch64Inst for LdrPost {
    fn encode_word(&self) -> u32 {
        (self.rt.ls_size() << 30)
            | 0x38400400
            | self.imm.bits() << 12
            | (self.rn.index() as u32) << 5
            | self.rt.index() as u32
    }
}

impl core::fmt::Display for LdrPost {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "ldr ")?;
        self.rt.fmt_reg(f)?;
        write!(f, ", [")?;
        self.rn.fmt_base(f)?;
        write!(f, "], #{}", self.imm.value())
    }
}
