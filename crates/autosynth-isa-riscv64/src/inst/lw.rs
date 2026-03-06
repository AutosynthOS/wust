use crate::imm::SImm12;
use crate::reg::Gpr;

use super::Rv64Inst;

/// `LW rd, offset(rs1)` -- load 32-bit word, sign-extend to 64 bits.
///
/// I-type: opcode=0x03, funct3=2.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Lw {
    pub rd: Gpr,
    pub rs1: Gpr,
    pub imm: SImm12,
}

impl Rv64Inst for Lw {
    fn encode_word(&self) -> u32 {
        self.imm.bits() << 20
            | (self.rs1.index() as u32) << 15
            | (2u32 << 12)
            | (self.rd.index() as u32) << 7
            | 0x03
    }
}

impl core::fmt::Display for Lw {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "lw {}, {}({})", self.rd, self.imm.value(), self.rs1)
    }
}
