use super::X86_64Inst;

/// `RET` -- return from procedure.
///
/// Single-byte opcode 0xC3.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ret;

impl X86_64Inst for Ret {
    fn encode_bytes(&self, buf: &mut [u8]) -> usize {
        buf[0] = 0xC3;
        1
    }
}

impl core::fmt::Display for Ret {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "ret")
    }
}
