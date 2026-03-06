use crate::reg::Gpr;

use super::Rv64Inst;

/// `SUBW rd, rs1, rs2` -- 32-bit register subtraction, sign-extending result.
///
/// R-type: opcode=0x3B, funct3=0, funct7=0x20.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Subw {
    pub rd: Gpr,
    pub rs1: Gpr,
    pub rs2: Gpr,
}

impl Rv64Inst for Subw {
    fn encode_word(&self) -> u32 {
        (0x20u32 << 25)
            | (self.rs2.index() as u32) << 20
            | (self.rs1.index() as u32) << 15
            | (self.rd.index() as u32) << 7
            | 0x3B
    }
}

impl core::fmt::Display for Subw {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "subw {}, {}, {}", self.rd, self.rs1, self.rs2)
    }
}
