use crate::encode::{emit_alu_imm8, emit_alu_imm32};
use crate::imm::Imm32;
use crate::reg::Gpr;

use super::X86_64Inst;

/// `ADD r/m, imm` -- add immediate to register.
///
/// Uses imm8 (sign-extended) when possible, otherwise imm32.
/// Extension opcode /0.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AddRegImm {
    pub dst: Gpr,
    pub imm: Imm32,
}

impl X86_64Inst for AddRegImm {
    fn encode_bytes(&self, buf: &mut [u8]) -> usize {
        if self.imm.fits_imm8() {
            emit_alu_imm8(
                buf,
                0, // /0 = ADD
                self.dst.is_64(),
                self.dst.is_extended(),
                self.dst.low3(),
                self.imm.value() as u8,
            )
        } else {
            emit_alu_imm32(
                buf,
                0,
                self.dst.is_64(),
                self.dst.is_extended(),
                self.dst.low3(),
                self.imm.value(),
            )
        }
    }
}

impl core::fmt::Display for AddRegImm {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "add {}, {}", self.dst, self.imm.value())
    }
}
