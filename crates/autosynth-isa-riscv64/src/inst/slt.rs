use crate::reg::Gpr;

use super::Rv64Inst;

/// `SLT rd, rs1, rs2` -- set less than (signed).
///
/// R-type: opcode=0x33, funct3=2, funct7=0.
/// Sets rd to 1 if rs1 < rs2 (signed), else 0.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Slt {
    pub rd: Gpr,
    pub rs1: Gpr,
    pub rs2: Gpr,
}

impl Rv64Inst for Slt {
    fn encode_word(&self) -> u32 {
        (self.rs2.index() as u32) << 20
            | (self.rs1.index() as u32) << 15
            | (2u32 << 12)
            | (self.rd.index() as u32) << 7
            | 0x33
    }
}

impl core::fmt::Display for Slt {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "slt {}, {}, {}", self.rd, self.rs1, self.rs2)
    }
}
