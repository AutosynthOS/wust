use autosynth_isa::SImm26;

use super::Aarch64Inst;

/// `B <offset>` — unconditional branch.
///
/// Signed 26-bit word offset (±128MB range).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct B {
    pub offset: SImm26,
}

impl Aarch64Inst for B {
    fn encode_word(&self) -> u32 {
        0x14000000 | self.offset.bits()
    }
}

impl core::fmt::Display for B {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "b #{}", self.offset.value() * 4)
    }
}
