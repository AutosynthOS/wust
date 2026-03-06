use crate::encode::rex;
use crate::reg::Gpr;

use super::X86_64Inst;

/// `MOV r, imm` -- load immediate into register.
///
/// For 32-bit registers: `MOV r32, imm32` (opcode 0xB8+rd).
/// For 64-bit registers with values that fit in i32: `MOV r/m64, imm32`
/// (sign-extended, REX.W + 0xC7 /0).
/// For 64-bit registers with large values: `MOV r64, imm64`
/// (REX.W + 0xB8+rd + imm64).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MovRegImm {
    pub dst: Gpr,
    pub imm: i64,
}

impl X86_64Inst for MovRegImm {
    fn encode_bytes(&self, buf: &mut [u8]) -> usize {
        match self.dst {
            Gpr::R32(r) => {
                // MOV r32, imm32: [REX?] 0xB8+rd imm32
                let mut i = 0;
                if r.is_extended() {
                    buf[i] = rex(false, false, false, true);
                    i += 1;
                }
                buf[i] = 0xB8 + r.low3();
                i += 1;
                let bytes = (self.imm as u32).to_le_bytes();
                buf[i..i + 4].copy_from_slice(&bytes);
                i + 4
            }
            Gpr::R64(r) => {
                let val = self.imm;
                if val >= i32::MIN as i64 && val <= i32::MAX as i64 {
                    // MOV r/m64, imm32 (sign-extended): REX.W 0xC7 ModR/M(11, /0, rd) imm32
                    let mut i = 0;
                    buf[i] = rex(true, false, false, r.is_extended());
                    i += 1;
                    buf[i] = 0xC7;
                    i += 1;
                    buf[i] = crate::encode::modrm(0b11, 0, r.low3());
                    i += 1;
                    let bytes = (val as i32).to_le_bytes();
                    buf[i..i + 4].copy_from_slice(&bytes);
                    i + 4
                } else {
                    // MOV r64, imm64: REX.W 0xB8+rd imm64
                    let mut i = 0;
                    buf[i] = rex(true, false, false, r.is_extended());
                    i += 1;
                    buf[i] = 0xB8 + r.low3();
                    i += 1;
                    let bytes = val.to_le_bytes();
                    buf[i..i + 8].copy_from_slice(&bytes);
                    i + 8
                }
            }
        }
    }
}

impl core::fmt::Display for MovRegImm {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "mov {}, {}", self.dst, self.imm)
    }
}
