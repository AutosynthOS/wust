use crate::imm::JImm21;
use crate::reg::Gpr;

use super::Rv64Inst;

/// `JAL rd, offset` -- jump and link.
///
/// J-type: opcode=0x6F.
/// `JAL ra, offset` is a function call.
/// `JAL zero, offset` is an unconditional jump (J pseudo-instruction).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Jal {
    pub rd: Gpr,
    pub imm: JImm21,
}

impl Rv64Inst for Jal {
    fn encode_word(&self) -> u32 {
        self.imm.encode_j_type()
            | (self.rd.index() as u32) << 7
            | 0x6F
    }
}

impl core::fmt::Display for Jal {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "jal {}, {}", self.rd, self.imm.value())
    }
}
