use super::Aarch64Inst;

/// `BL <offset>` — branch with link (call).
///
/// Signed 26-bit word offset (±128MB range).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Bl {
    /// Signed word offset from this instruction.
    pub offset: i32,
}

impl Aarch64Inst for Bl {
    fn encode_word(&self) -> u32 {
        let imm26 = (self.offset as u32) & 0x03FF_FFFF;
        0x94000000 | imm26
    }
}

impl core::fmt::Display for Bl {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "bl #{}", self.offset * 4)
    }
}
