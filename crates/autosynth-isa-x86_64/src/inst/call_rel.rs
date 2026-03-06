use super::X86_64Inst;

/// `CALL rel32` -- relative call.
///
/// Opcode: 0xE8 followed by a signed 32-bit relative offset.
/// The offset is relative to the end of this instruction (5 bytes).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CallRel32 {
    /// Signed 32-bit byte offset from the end of this instruction.
    pub offset: i32,
}

impl X86_64Inst for CallRel32 {
    fn encode_bytes(&self, buf: &mut [u8]) -> usize {
        buf[0] = 0xE8;
        let bytes = self.offset.to_le_bytes();
        buf[1..5].copy_from_slice(&bytes);
        5
    }
}

impl core::fmt::Display for CallRel32 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "call {}", self.offset)
    }
}
