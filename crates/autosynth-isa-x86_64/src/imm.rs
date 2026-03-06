/// Error returned when an immediate value is out of range for its type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ImmOutOfRange;

impl core::fmt::Display for ImmOutOfRange {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "immediate value out of range")
    }
}

/// 8-bit signed immediate (-128 to 127).
///
/// Used by ALU instructions with sign-extended imm8 encoding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Imm8(i8);

impl Imm8 {
    pub const fn new(val: i8) -> Self {
        Imm8(val)
    }

    pub const fn value(self) -> i8 {
        self.0
    }

    /// Encode as a single byte.
    pub const fn byte(self) -> u8 {
        self.0 as u8
    }
}

/// 32-bit signed immediate.
///
/// Used by ALU instructions with imm32 encoding and MOV immediate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Imm32(i32);

impl Imm32 {
    pub const fn new(val: i32) -> Self {
        Imm32(val)
    }

    pub const fn value(self) -> i32 {
        self.0
    }

    /// Whether this value fits in a sign-extended imm8.
    pub const fn fits_imm8(self) -> bool {
        self.0 >= -128 && self.0 <= 127
    }

    /// Encode as 4 little-endian bytes.
    pub const fn bytes(self) -> [u8; 4] {
        self.0.to_le_bytes()
    }
}
