use crate::encode::emit_reg_reg;
use crate::reg::Gpr;

use super::X86_64Inst;

/// `MOV r/m, r` -- register-to-register move.
///
/// Width is derived from the registers (must match).
/// Opcode: 0x89 (mov r/m, r).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MovRegReg {
    pub dst: Gpr,
    pub src: Gpr,
}

impl X86_64Inst for MovRegReg {
    fn encode_bytes(&self, buf: &mut [u8]) -> usize {
        emit_reg_reg(
            buf,
            0x89,
            self.dst.is_64(),
            self.src.is_extended(),
            self.dst.is_extended(),
            self.src.low3(),
            self.dst.low3(),
        )
    }
}

impl core::fmt::Display for MovRegReg {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "mov {}, {}", self.dst, self.src)
    }
}
