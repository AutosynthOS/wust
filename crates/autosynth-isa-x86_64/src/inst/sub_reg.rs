use crate::encode::emit_reg_reg;
use crate::reg::Gpr;

use super::X86_64Inst;

/// `SUB r/m, r` -- register-register subtract.
///
/// Width is derived from the registers (must match).
/// Opcode: 0x29 (sub r/m, r) for 32-bit, REX.W + 0x29 for 64-bit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SubRegReg {
    pub dst: Gpr,
    pub src: Gpr,
}

impl X86_64Inst for SubRegReg {
    fn encode_bytes(&self, buf: &mut [u8]) -> usize {
        emit_reg_reg(
            buf,
            0x29,
            self.dst.is_64(),
            self.src.is_extended(),
            self.dst.is_extended(),
            self.src.low3(),
            self.dst.low3(),
        )
    }
}

impl core::fmt::Display for SubRegReg {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "sub {}, {}", self.dst, self.src)
    }
}
