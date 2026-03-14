use autosynth_isa::SImm19;

use crate::cond::Cond;

use super::Aarch64Inst;

/// `B.cond <offset>` — conditional branch.
///
/// The offset is a signed word offset from this instruction
/// (±1MB range, 19-bit signed).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BCond {
    pub cond: Cond,
    pub offset: SImm19,
}

impl Aarch64Inst for BCond {
    fn encode_word(&self) -> u32 {
        0x54000000 | (self.offset.bits() << 5) | self.cond as u32
    }
}

impl core::fmt::Display for BCond {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "b.{} #{}", self.cond, self.offset.value() * 4)
    }
}
