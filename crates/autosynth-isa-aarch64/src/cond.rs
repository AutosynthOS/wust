/// AArch64 condition codes for conditional branches and selects.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Cond {
    /// Equal (Z == 1).
    EQ = 0b0000,
    /// Not equal (Z == 0).
    NE = 0b0001,
    /// Carry set / unsigned higher or same (C == 1).
    CS = 0b0010,
    /// Carry clear / unsigned lower (C == 0).
    CC = 0b0011,
    /// Minus / negative (N == 1).
    MI = 0b0100,
    /// Plus / positive or zero (N == 0).
    PL = 0b0101,
    /// Overflow (V == 1).
    VS = 0b0110,
    /// No overflow (V == 0).
    VC = 0b0111,
    /// Unsigned higher (C == 1 && Z == 0).
    HI = 0b1000,
    /// Unsigned lower or same (C == 0 || Z == 1).
    LS = 0b1001,
    /// Signed greater or equal (N == V).
    GE = 0b1010,
    /// Signed less than (N != V).
    LT = 0b1011,
    /// Signed greater than (Z == 0 && N == V).
    GT = 0b1100,
    /// Signed less or equal (Z == 1 || N != V).
    LE = 0b1101,
    /// Always (unconditional).
    AL = 0b1110,
}

impl Cond {
    /// Invert the condition (e.g., LE → GT, EQ → NE).
    pub const fn invert(self) -> Self {
        // On aarch64, inverting a condition flips bit 0.
        let bits = (self as u8) ^ 1;
        // Safety: all 4-bit values with bit 0 flipped map to valid variants.
        unsafe { core::mem::transmute(bits) }
    }

    /// Decode from a 4-bit condition field.
    pub const fn from_bits(bits: u8) -> Option<Self> {
        if bits > 0b1110 {
            None
        } else {
            Some(unsafe { core::mem::transmute(bits) })
        }
    }
}

impl core::fmt::Display for Cond {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let s = match self {
            Cond::EQ => "eq",
            Cond::NE => "ne",
            Cond::CS => "cs",
            Cond::CC => "cc",
            Cond::MI => "mi",
            Cond::PL => "pl",
            Cond::VS => "vs",
            Cond::VC => "vc",
            Cond::HI => "hi",
            Cond::LS => "ls",
            Cond::GE => "ge",
            Cond::LT => "lt",
            Cond::GT => "gt",
            Cond::LE => "le",
            Cond::AL => "al",
        };
        write!(f, "{s}")
    }
}
