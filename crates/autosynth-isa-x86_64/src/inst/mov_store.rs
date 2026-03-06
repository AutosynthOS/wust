use crate::encode::{emit_mem, rex};
use crate::reg::{Gpr, Gpr64};

use super::X86_64Inst;

/// `MOV [base + disp], r` -- store to memory.
///
/// Opcode: 0x89 (mov r/m, r).
/// Width is derived from `src`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MovStore {
    pub base: Gpr64,
    pub disp: i32,
    pub src: Gpr,
}

impl X86_64Inst for MovStore {
    fn encode_bytes(&self, buf: &mut [u8]) -> usize {
        let mut i = 0;
        let is_64 = self.src.is_64();
        let reg_ext = self.src.is_extended();
        let base_ext = self.base.is_extended();

        if is_64 || reg_ext || base_ext {
            buf[i] = rex(is_64, reg_ext, false, base_ext);
            i += 1;
        }
        buf[i] = 0x89;
        i += 1;

        let n = emit_mem(buf, i, self.src.low3(), self.base.low3(), base_ext, self.disp);
        i + n
    }
}

impl core::fmt::Display for MovStore {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if self.disp == 0 {
            write!(f, "mov [{}], {}", self.base, self.src)
        } else {
            write!(f, "mov [{} + {}], {}", self.base, self.disp, self.src)
        }
    }
}
