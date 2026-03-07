use crate::reg::Gpr;

use super::Rv64Inst;

/// `SLTU rd, rs1, rs2` -- set less than (unsigned).
///
/// R-type: opcode=0x33, funct3=3, funct7=0.
/// Sets rd to 1 if rs1 < rs2 (unsigned), else 0.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Sltu {
    pub rd: Gpr,
    pub rs1: Gpr,
    pub rs2: Gpr,
}

impl Rv64Inst for Sltu {
    fn encode_word(&self) -> u32 {
        (self.rs2.index() as u32) << 20
            | (self.rs1.index() as u32) << 15
            | (3u32 << 12)
            | (self.rd.index() as u32) << 7
            | 0x33
    }
}

impl core::fmt::Display for Sltu {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "sltu {}, {}, {}", self.rd, self.rs1, self.rs2)
    }
}
