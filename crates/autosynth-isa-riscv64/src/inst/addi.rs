use crate::imm::SImm12;
use crate::reg::Gpr;

use super::Rv64Inst;

/// `ADDI rd, rs1, imm` -- add 12-bit signed immediate (64-bit).
///
/// I-type: opcode=0x13, funct3=0.
/// Also encodes `MV rd, rs1` (imm=0) and `NOP` (rd=x0, rs1=x0, imm=0).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Addi {
    pub rd: Gpr,
    pub rs1: Gpr,
    pub imm: SImm12,
}

impl Rv64Inst for Addi {
    fn encode_word(&self) -> u32 {
        self.imm.bits() << 20
            | (self.rs1.index() as u32) << 15
            | (self.rd.index() as u32) << 7
            | 0x13
    }
}

impl core::fmt::Display for Addi {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "addi {}, {}, {}", self.rd, self.rs1, self.imm.value())
    }
}
