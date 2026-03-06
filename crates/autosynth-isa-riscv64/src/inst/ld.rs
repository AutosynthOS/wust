use crate::imm::SImm12;
use crate::reg::Gpr;

use super::Rv64Inst;

/// `LD rd, offset(rs1)` -- load 64-bit doubleword.
///
/// I-type: opcode=0x03, funct3=3.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ld {
    pub rd: Gpr,
    pub rs1: Gpr,
    pub imm: SImm12,
}

impl Rv64Inst for Ld {
    fn encode_word(&self) -> u32 {
        self.imm.bits() << 20
            | (self.rs1.index() as u32) << 15
            | (3u32 << 12)
            | (self.rd.index() as u32) << 7
            | 0x03
    }
}

impl core::fmt::Display for Ld {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "ld {}, {}({})", self.rd, self.imm.value(), self.rs1)
    }
}
