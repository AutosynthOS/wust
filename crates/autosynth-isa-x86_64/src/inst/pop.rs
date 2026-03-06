use crate::encode::rex;
use crate::reg::Gpr64;

use super::X86_64Inst;

/// `POP r64` -- pop from the stack into register.
///
/// Always 64-bit in 64-bit mode.
/// Opcode: 0x58+rd, with REX.B for r8-r15.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pop {
    pub dst: Gpr64,
}

impl X86_64Inst for Pop {
    fn encode_bytes(&self, buf: &mut [u8]) -> usize {
        let mut i = 0;
        if self.dst.is_extended() {
            buf[i] = rex(false, false, false, true);
            i += 1;
        }
        buf[i] = 0x58 + self.dst.low3();
        i + 1
    }
}

impl core::fmt::Display for Pop {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "pop {}", self.dst)
    }
}
