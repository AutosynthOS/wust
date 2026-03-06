use crate::reg::Gpr;

use super::Rv64Inst;

/// `OR rd, rs1, rs2` -- bitwise OR.
///
/// R-type: opcode=0x33, funct3=6, funct7=0.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Or {
    pub rd: Gpr,
    pub rs1: Gpr,
    pub rs2: Gpr,
}

impl Rv64Inst for Or {
    fn encode_word(&self) -> u32 {
        (self.rs2.index() as u32) << 20
            | (self.rs1.index() as u32) << 15
            | (6u32 << 12)
            | (self.rd.index() as u32) << 7
            | 0x33
    }
}

impl core::fmt::Display for Or {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "or {}, {}, {}", self.rd, self.rs1, self.rs2)
    }
}
