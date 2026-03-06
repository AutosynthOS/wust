use crate::encode::emit_reg_reg;
use crate::reg::Gpr;

use super::X86_64Inst;

/// `ADD r/m, r` -- register-register add.
///
/// Width is derived from the registers (must match).
/// Opcode: 0x01 (add r/m, r) for 32-bit, REX.W + 0x01 for 64-bit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AddRegReg {
    pub dst: Gpr,
    pub src: Gpr,
}

impl X86_64Inst for AddRegReg {
    fn encode_bytes(&self, buf: &mut [u8]) -> usize {
        emit_reg_reg(
            buf,
            0x01,
            self.dst.is_64(),
            self.src.is_extended(),
            self.dst.is_extended(),
            self.src.low3(),
            self.dst.low3(),
        )
    }
}

impl core::fmt::Display for AddRegReg {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "add {}, {}", self.dst, self.src)
    }
}
