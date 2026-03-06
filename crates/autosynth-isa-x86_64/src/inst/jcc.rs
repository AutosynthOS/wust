use crate::cond::Cond;

use super::X86_64Inst;

/// `Jcc rel32` -- conditional jump (near).
///
/// Opcode: 0x0F (0x80+cc) followed by a signed 32-bit relative offset.
/// The offset is relative to the end of this instruction (6 bytes).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Jcc {
    pub cond: Cond,
    /// Signed 32-bit byte offset from the end of this instruction.
    pub offset: i32,
}

impl X86_64Inst for Jcc {
    fn encode_bytes(&self, buf: &mut [u8]) -> usize {
        buf[0] = 0x0F;
        buf[1] = 0x80 + self.cond.code();
        let bytes = self.offset.to_le_bytes();
        buf[2..6].copy_from_slice(&bytes);
        6
    }
}

impl core::fmt::Display for Jcc {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "j{} {}", self.cond, self.offset)
    }
}
