use crate::imm::SImm20;
use crate::reg::Gpr;

use super::Rv64Inst;

/// `LUI rd, imm` -- load upper immediate.
///
/// U-type: opcode=0x37. Places the 20-bit immediate into bits [31:12]
/// of rd, sign-extending to 64 bits, with bits [11:0] zeroed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Lui {
    pub rd: Gpr,
    pub imm: SImm20,
}

impl Rv64Inst for Lui {
    fn encode_word(&self) -> u32 {
        self.imm.bits() << 12
            | (self.rd.index() as u32) << 7
            | 0x37
    }
}

impl core::fmt::Display for Lui {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "lui {}, {}", self.rd, self.imm.value())
    }
}
