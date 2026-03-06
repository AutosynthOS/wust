use crate::imm::UImm12;
use crate::reg::{GprOrZr, GprOrSp};

use super::Aarch64Inst;

/// `STR Rt, [Rn, #imm]` — store with unsigned scaled offset.
///
/// Width and scale are derived from `rt`. The offset is a raw 12-bit
/// immediate; the hardware scales it by the byte size (4 for W, 8 for X).
///
/// `Rt` is GprOrZr (31 = ZR). `Rn` is always a 64-bit base (GprOrSp).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StrUoff {
    pub rt: GprOrZr,
    pub rn: GprOrSp,
    /// Raw 12-bit offset (0–4095). Byte offset = value × rt.byte_size().
    pub offset: UImm12,
}

impl Aarch64Inst for StrUoff {
    fn encode_word(&self) -> u32 {
        (self.rt.ls_size() << 30)
            | 0x39000000
            | (self.offset.value() as u32) << 10
            | (self.rn.index() as u32) << 5
            | self.rt.index() as u32
    }
}

impl core::fmt::Display for StrUoff {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let byte_off = self.offset.value() as u32 * self.rt.byte_size() as u32;
        write!(f, "str ")?;
        self.rt.fmt_reg(f)?;
        write!(f, ", [")?;
        self.rn.fmt_base(f)?;
        if byte_off == 0 { write!(f, "]") } else { write!(f, ", #{byte_off}]") }
    }
}
