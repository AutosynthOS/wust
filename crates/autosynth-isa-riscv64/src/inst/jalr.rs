use crate::imm::SImm12;
use crate::reg::Gpr;

use super::Rv64Inst;

/// `JALR rd, rs1, offset` -- jump and link register.
///
/// I-type: opcode=0x67, funct3=0.
/// `JALR zero, ra, 0` is `RET`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Jalr {
    pub rd: Gpr,
    pub rs1: Gpr,
    pub imm: SImm12,
}

impl Rv64Inst for Jalr {
    fn encode_word(&self) -> u32 {
        self.imm.bits() << 20
            | (self.rs1.index() as u32) << 15
            | (self.rd.index() as u32) << 7
            | 0x67
    }
}

impl core::fmt::Display for Jalr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "jalr {}, {}, {}", self.rd, self.rs1, self.imm.value())
    }
}
