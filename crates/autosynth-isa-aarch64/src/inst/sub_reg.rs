use crate::reg::GprOrZr;

use super::Aarch64Inst;

/// `SUB Rd, Rn, Rm` — subtract register.
///
/// Register 31 in any position means ZR (zero register).
/// Width is derived from the registers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SubReg {
    pub rd: GprOrZr,
    pub rn: GprOrZr,
    pub rm: GprOrZr,
}

impl Aarch64Inst for SubReg {
    fn encode_word(&self) -> u32 {
        (self.rd.sf() << 31)
            | 0x4B000000
            | (self.rm.index() as u32) << 16
            | (self.rn.index() as u32) << 5
            | self.rd.index() as u32
    }
}

impl core::fmt::Display for SubReg {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "sub ")?;
        self.rd.fmt_reg(f)?;
        write!(f, ", ")?;
        self.rn.fmt_reg(f)?;
        write!(f, ", ")?;
        self.rm.fmt_reg(f)
    }
}
