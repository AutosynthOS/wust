use crate::imm::BImm13;
use crate::reg::Gpr;

use super::Rv64Inst;

/// `BGEU rs1, rs2, offset` -- branch if greater than or equal (unsigned).
///
/// B-type: opcode=0x63, funct3=7.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Bgeu {
    pub rs1: Gpr,
    pub rs2: Gpr,
    pub imm: BImm13,
}

impl Rv64Inst for Bgeu {
    fn encode_word(&self) -> u32 {
        self.imm.encode_b_type()
            | (self.rs2.index() as u32) << 20
            | (self.rs1.index() as u32) << 15
            | (7u32 << 12)
            | 0x63
    }
}

impl core::fmt::Display for Bgeu {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "bgeu {}, {}, {}", self.rs1, self.rs2, self.imm.value())
    }
}
