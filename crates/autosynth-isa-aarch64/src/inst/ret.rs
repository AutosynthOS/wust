use crate::reg::XGpr;

use super::Aarch64Inst;

/// `RET {Xn}` — return to address in register.
///
/// Default is X30 (the link register). Always 64-bit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ret {
    pub rn: XGpr,
}

impl Ret {
    /// `RET` — return to X30 (link register).
    pub const fn new() -> Self {
        Ret { rn: XGpr::R30 }
    }
}

impl Aarch64Inst for Ret {
    fn encode_word(&self) -> u32 {
        0xD65F0000 | (self.rn.index() as u32) << 5
    }
}

impl core::fmt::Display for Ret {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if self.rn == XGpr::R30 {
            write!(f, "ret")
        } else {
            write!(f, "ret x{}", self.rn.index())
        }
    }
}
