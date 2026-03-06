use crate::imm::UImm16;
use crate::reg::GprOrZr;

use super::Aarch64Inst;

/// `MOVZ Rd, #imm16 {, LSL #shift}` — move 16-bit immediate, zero rest.
///
/// Width is derived from `rd`.
/// `hw` is the shift amount in units of 16 bits (0–1 for W, 0–3 for X).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Movz {
    pub rd: GprOrZr,
    pub imm: UImm16,
    pub hw: u8,
}

impl Aarch64Inst for Movz {
    fn encode_word(&self) -> u32 {
        (self.rd.sf() << 31)
            | 0x52800000
            | (self.hw as u32 & 0x3) << 21
            | (self.imm.value() as u32) << 5
            | self.rd.index() as u32
    }
}

impl core::fmt::Display for Movz {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let shift = self.hw as u32 * 16;
        write!(f, "movz ")?;
        self.rd.fmt_reg(f)?;
        if shift == 0 {
            write!(f, ", #{}", self.imm.value())
        } else {
            write!(f, ", #{}, lsl #{shift}", self.imm.value())
        }
    }
}
