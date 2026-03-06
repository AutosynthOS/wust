/// Error returned when an immediate value is out of range for its type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ImmOutOfRange;

impl core::fmt::Display for ImmOutOfRange {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "immediate value out of range")
    }
}

/// 12-bit unsigned immediate (0–4095).
///
/// Used by ADD/SUB immediate instructions and as the raw (pre-scale)
/// offset field in load/store unsigned-offset instructions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UImm12(u16);

impl UImm12 {
    pub const fn new(val: u16) -> Result<Self, ImmOutOfRange> {
        if val > 4095 {
            Err(ImmOutOfRange)
        } else {
            Ok(UImm12(val))
        }
    }

    pub const fn value(self) -> u16 {
        self.0
    }
}

/// 16-bit unsigned immediate (0–65535).
///
/// Used by MOVZ/MOVK instructions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UImm16(u16);

impl UImm16 {
    pub const fn new(val: u16) -> Self {
        UImm16(val)
    }

    pub const fn value(self) -> u16 {
        self.0
    }
}

/// 9-bit signed immediate (−256 to +255).
///
/// Used by pre-index, post-index, and unscaled load/store instructions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SImm9(i16);

impl SImm9 {
    pub const fn new(val: i16) -> Result<Self, ImmOutOfRange> {
        if val < -256 || val > 255 {
            Err(ImmOutOfRange)
        } else {
            Ok(SImm9(val))
        }
    }

    pub const fn value(self) -> i16 {
        self.0
    }

    /// Encode as the 9-bit field used in instructions.
    pub const fn bits(self) -> u32 {
        (self.0 as u32) & 0x1FF
    }
}
