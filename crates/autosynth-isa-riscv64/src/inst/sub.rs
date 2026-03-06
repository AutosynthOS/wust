use crate::reg::Gpr;

use super::Rv64Inst;

/// `SUB rd, rs1, rs2` -- 64-bit register subtraction.
///
/// R-type: opcode=0x33, funct3=0, funct7=0x20.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Sub {
    pub rd: Gpr,
    pub rs1: Gpr,
    pub rs2: Gpr,
}

impl Rv64Inst for Sub {
    fn encode_word(&self) -> u32 {
        (0x20u32 << 25)
            | (self.rs2.index() as u32) << 20
            | (self.rs1.index() as u32) << 15
            | (self.rd.index() as u32) << 7
            | 0x33
    }
}

impl core::fmt::Display for Sub {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "sub {}, {}, {}", self.rd, self.rs1, self.rs2)
    }
}
