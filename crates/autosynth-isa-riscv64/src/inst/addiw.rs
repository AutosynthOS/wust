use crate::imm::SImm12;
use crate::reg::Gpr;

use super::Rv64Inst;

/// `ADDIW rd, rs1, imm` -- add 12-bit signed immediate (32-bit), sign-extend.
///
/// I-type: opcode=0x1B, funct3=0.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Addiw {
    pub rd: Gpr,
    pub rs1: Gpr,
    pub imm: SImm12,
}

impl Rv64Inst for Addiw {
    fn encode_word(&self) -> u32 {
        self.imm.bits() << 20
            | (self.rs1.index() as u32) << 15
            | (self.rd.index() as u32) << 7
            | 0x1B
    }
}

impl core::fmt::Display for Addiw {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "addiw {}, {}, {}", self.rd, self.rs1, self.imm.value())
    }
}
