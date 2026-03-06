use crate::imm::UImm12;
use crate::reg::GprOrSp;

use super::Aarch64Inst;

/// `ADD Rd, Rn, #imm12` — add unsigned 12-bit immediate.
///
/// Register 31 in Rd/Rn means SP (stack pointer), not ZR.
/// Width is derived from the registers (`WGpr` → 32-bit, `XGpr` → 64-bit).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AddImm {
    pub rd: GprOrSp,
    pub rn: GprOrSp,
    pub imm: UImm12,
}

impl AddImm {
    fn sf(&self) -> u32 {
        match (&self.rd, &self.rn) {
            (GprOrSp::Gpr(g), _) | (_, GprOrSp::Gpr(g)) => g.sf(),
            (GprOrSp::Sp, GprOrSp::Sp) => 1,
        }
    }
}

impl Aarch64Inst for AddImm {
    fn encode_word(&self) -> u32 {
        (self.sf() << 31)
            | 0x11000000
            | (self.imm.value() as u32) << 10
            | (self.rn.index() as u32) << 5
            | self.rd.index() as u32
    }
}

impl core::fmt::Display for AddImm {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "add ")?;
        self.rd.fmt_reg(f)?;
        write!(f, ", ")?;
        self.rn.fmt_reg(f)?;
        write!(f, ", #{}", self.imm.value())
    }
}
