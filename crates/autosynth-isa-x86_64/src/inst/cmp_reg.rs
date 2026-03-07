use crate::encode::emit_reg_reg;
use crate::reg::Gpr;

use super::X86_64Inst;

/// `CMP r/m, r` -- register-register compare.
///
/// Sets flags based on (dst - src) without storing the result.
/// Width is derived from the registers (must match).
/// Opcode: 0x39 (cmp r/m, r).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CmpRegReg {
    pub lhs: Gpr,
    pub rhs: Gpr,
}

impl X86_64Inst for CmpRegReg {
    fn encode_bytes(&self, buf: &mut [u8]) -> usize {
        emit_reg_reg(
            buf,
            0x39,
            self.lhs.is_64(),
            self.rhs.is_extended(),
            self.lhs.is_extended(),
            self.rhs.low3(),
            self.lhs.low3(),
        )
    }
}

impl core::fmt::Display for CmpRegReg {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "cmp {}, {}", self.lhs, self.rhs)
    }
}
