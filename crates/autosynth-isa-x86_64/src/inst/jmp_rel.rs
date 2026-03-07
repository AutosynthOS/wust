use super::X86_64Inst;

/// `JMP rel32` -- unconditional near jump.
///
/// Opcode: 0xE9 followed by a signed 32-bit relative offset.
/// The offset is relative to the end of this instruction (5 bytes).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct JmpRel32 {
    /// Signed 32-bit byte offset from the end of this instruction.
    pub offset: i32,
}

impl X86_64Inst for JmpRel32 {
    fn encode_bytes(&self, buf: &mut [u8]) -> usize {
        buf[0] = 0xE9;
        let bytes = self.offset.to_le_bytes();
        buf[1..5].copy_from_slice(&bytes);
        5
    }
}

impl core::fmt::Display for JmpRel32 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "jmp {}", self.offset)
    }
}
