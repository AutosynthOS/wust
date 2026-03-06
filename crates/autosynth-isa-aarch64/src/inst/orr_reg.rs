use crate::reg::GprOrZr;

use super::Aarch64Inst;

/// `ORR Rd, Rn, Rm` — bitwise OR register.
///
/// When Rn is WZR/XZR, this acts as `MOV Rd, Rm`.
/// Register 31 in any position means ZR (zero register).
/// Width is derived from the registers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OrrReg {
    pub rd: GprOrZr,
    pub rn: GprOrZr,
    pub rm: GprOrZr,
}

impl Aarch64Inst for OrrReg {
    fn encode_word(&self) -> u32 {
        (self.rd.sf() << 31)
            | 0x2A000000
            | (self.rm.index() as u32) << 16
            | (self.rn.index() as u32) << 5
            | self.rd.index() as u32
    }
}

impl core::fmt::Display for OrrReg {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "orr ")?;
        self.rd.fmt_reg(f)?;
        write!(f, ", ")?;
        self.rn.fmt_reg(f)?;
        write!(f, ", ")?;
        self.rm.fmt_reg(f)
    }
}
