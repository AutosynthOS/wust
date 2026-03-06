use crate::imm::UImm12;
use crate::reg::{GprOrSp, GprOrZr};

use super::Aarch64Inst;

/// `SUBS Rd, Rn, #imm12` — subtract immediate, setting flags.
///
/// `Rd` is GprOrZr (31 = WZR/XZR, used for CMP alias).
/// `Rn` is GprOrSp (31 = SP).
/// Width is derived from the registers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SubsImm {
    pub rd: GprOrZr,
    pub rn: GprOrSp,
    pub imm: UImm12,
}

impl SubsImm {
    /// Derive the sf bit. Check rd first; if it's a Gpr, use its sf.
    /// If rd is Wzr, sf=0. If rd is Xzr, sf=1. Otherwise fall back to rn.
    fn sf(&self) -> u32 {
        self.rd.sf()
    }
}

impl Aarch64Inst for SubsImm {
    fn encode_word(&self) -> u32 {
        (self.sf() << 31)
            | 0x71000000
            | (self.imm.value() as u32) << 10
            | (self.rn.index() as u32) << 5
            | self.rd.index() as u32
    }
}

impl core::fmt::Display for SubsImm {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "subs ")?;
        self.rd.fmt_reg(f)?;
        write!(f, ", ")?;
        self.rn.fmt_reg(f)?;
        write!(f, ", #{}", self.imm.value())
    }
}
