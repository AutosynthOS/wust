use crate::reg::GprOrZr;

use super::Aarch64Inst;

/// `SUBS Rd, Rn, Rm` — subtract register, setting flags.
///
/// When `Rd` is WZR/XZR this is the `CMP Rn, Rm` alias.
/// Width is derived from the registers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SubsReg {
    pub rd: GprOrZr,
    pub rn: GprOrZr,
    pub rm: GprOrZr,
}

impl Aarch64Inst for SubsReg {
    fn encode_word(&self) -> u32 {
        (self.rd.sf() << 31)
            | 0x6B000000
            | (self.rm.index() as u32) << 16
            | (self.rn.index() as u32) << 5
            | self.rd.index() as u32
    }
}

impl core::fmt::Display for SubsReg {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "subs ")?;
        self.rd.fmt_reg(f)?;
        write!(f, ", ")?;
        self.rn.fmt_reg(f)?;
        write!(f, ", ")?;
        self.rm.fmt_reg(f)
    }
}
