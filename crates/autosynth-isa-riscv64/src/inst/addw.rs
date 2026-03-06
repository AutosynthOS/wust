use crate::reg::Gpr;

use super::Rv64Inst;

/// `ADDW rd, rs1, rs2` -- 32-bit register addition, sign-extending result.
///
/// R-type: opcode=0x3B, funct3=0, funct7=0.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Addw {
    pub rd: Gpr,
    pub rs1: Gpr,
    pub rs2: Gpr,
}

impl Rv64Inst for Addw {
    fn encode_word(&self) -> u32 {
        (self.rs2.index() as u32) << 20
            | (self.rs1.index() as u32) << 15
            | (self.rd.index() as u32) << 7
            | 0x3B
    }
}

impl core::fmt::Display for Addw {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "addw {}, {}, {}", self.rd, self.rs1, self.rs2)
    }
}
