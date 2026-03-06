use crate::imm::SImm12;
use crate::reg::Gpr;

use super::Rv64Inst;

/// `SW rs2, offset(rs1)` -- store 32-bit word.
///
/// S-type: opcode=0x23, funct3=2.
/// Immediate is split: imm[11:5] in bits [31:25], imm[4:0] in bits [11:7].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Sw {
    pub rs2: Gpr,
    pub rs1: Gpr,
    pub imm: SImm12,
}

impl Rv64Inst for Sw {
    fn encode_word(&self) -> u32 {
        let imm = self.imm.bits();
        let imm_11_5 = (imm >> 5) & 0x7F;
        let imm_4_0 = imm & 0x1F;
        (imm_11_5 << 25)
            | (self.rs2.index() as u32) << 20
            | (self.rs1.index() as u32) << 15
            | (2u32 << 12)
            | (imm_4_0 << 7)
            | 0x23
    }
}

impl core::fmt::Display for Sw {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "sw {}, {}({})", self.rs2, self.imm.value(), self.rs1)
    }
}
