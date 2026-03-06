use crate::encode::{emit_mem, rex};
use crate::reg::{Gpr, Gpr64};

use super::X86_64Inst;

/// `MOV r, [base + disp]` -- load from memory.
///
/// Opcode: 0x8B (mov r, r/m).
/// Width is derived from `dst`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MovLoad {
    pub dst: Gpr,
    pub base: Gpr64,
    pub disp: i32,
}

impl X86_64Inst for MovLoad {
    fn encode_bytes(&self, buf: &mut [u8]) -> usize {
        let mut i = 0;
        let is_64 = self.dst.is_64();
        let reg_ext = self.dst.is_extended();
        let base_ext = self.base.is_extended();

        if is_64 || reg_ext || base_ext {
            buf[i] = rex(is_64, reg_ext, false, base_ext);
            i += 1;
        }
        buf[i] = 0x8B;
        i += 1;

        let n = emit_mem(buf, i, self.dst.low3(), self.base.low3(), base_ext, self.disp);
        i + n
    }
}

impl core::fmt::Display for MovLoad {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if self.disp == 0 {
            write!(f, "mov {}, [{}]", self.dst, self.base)
        } else {
            write!(f, "mov {}, [{} + {}]", self.dst, self.base, self.disp)
        }
    }
}
