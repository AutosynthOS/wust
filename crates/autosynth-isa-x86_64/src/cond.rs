/// x86_64 condition codes for conditional jumps (Jcc) and CMOVcc.
///
/// Values correspond to the 4-bit condition field in the opcode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Cond {
    /// Overflow (OF=1).
    O = 0x0,
    /// No overflow (OF=0).
    NO = 0x1,
    /// Below / carry (CF=1).
    B = 0x2,
    /// Above or equal / no carry (CF=0).
    AE = 0x3,
    /// Equal / zero (ZF=1).
    E = 0x4,
    /// Not equal / not zero (ZF=0).
    NE = 0x5,
    /// Below or equal (CF=1 or ZF=1).
    BE = 0x6,
    /// Above (CF=0 and ZF=0).
    A = 0x7,
    /// Sign (SF=1).
    S = 0x8,
    /// Not sign (SF=0).
    NS = 0x9,
    /// Parity even (PF=1).
    P = 0xA,
    /// Parity odd (PF=0).
    NP = 0xB,
    /// Less (SF!=OF).
    L = 0xC,
    /// Greater or equal (SF=OF).
    GE = 0xD,
    /// Less or equal (ZF=1 or SF!=OF).
    LE = 0xE,
    /// Greater (ZF=0 and SF=OF).
    G = 0xF,
}

impl Cond {
    /// Invert the condition (e.g., LE -> G, E -> NE).
    pub const fn invert(self) -> Self {
        let bits = (self as u8) ^ 1;
        // Safety: all 4-bit values with bit 0 flipped map to valid variants.
        unsafe { core::mem::transmute(bits) }
    }

    /// 4-bit condition code value.
    pub const fn code(self) -> u8 {
        self as u8
    }
}

impl core::fmt::Display for Cond {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let s = match self {
            Cond::O => "o",
            Cond::NO => "no",
            Cond::B => "b",
            Cond::AE => "ae",
            Cond::E => "e",
            Cond::NE => "ne",
            Cond::BE => "be",
            Cond::A => "a",
            Cond::S => "s",
            Cond::NS => "ns",
            Cond::P => "p",
            Cond::NP => "np",
            Cond::L => "l",
            Cond::GE => "ge",
            Cond::LE => "le",
            Cond::G => "g",
        };
        write!(f, "{s}")
    }
}
