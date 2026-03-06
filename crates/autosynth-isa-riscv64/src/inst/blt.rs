use crate::imm::BImm13;
use crate::reg::Gpr;

use super::Rv64Inst;

/// `BLT rs1, rs2, offset` -- branch if less than (signed).
///
/// B-type: opcode=0x63, funct3=4.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Blt {
    pub rs1: Gpr,
    pub rs2: Gpr,
    pub imm: BImm13,
}

impl Rv64Inst for Blt {
    fn encode_word(&self) -> u32 {
        self.imm.encode_b_type()
            | (self.rs2.index() as u32) << 20
            | (self.rs1.index() as u32) << 15
            | (4u32 << 12)
            | 0x63
    }
}

impl core::fmt::Display for Blt {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "blt {}, {}, {}", self.rs1, self.rs2, self.imm.value())
    }
}
