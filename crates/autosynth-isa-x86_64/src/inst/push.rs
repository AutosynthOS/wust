use crate::encode::rex;
use crate::reg::Gpr64;

use super::X86_64Inst;

/// `PUSH r64` -- push register onto the stack.
///
/// Always 64-bit in 64-bit mode.
/// Opcode: 0x50+rd, with REX.B for r8-r15.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Push {
    pub src: Gpr64,
}

impl X86_64Inst for Push {
    fn encode_bytes(&self, buf: &mut [u8]) -> usize {
        let mut i = 0;
        if self.src.is_extended() {
            buf[i] = rex(false, false, false, true);
            i += 1;
        }
        buf[i] = 0x50 + self.src.low3();
        i + 1
    }
}

impl core::fmt::Display for Push {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "push {}", self.src)
    }
}
