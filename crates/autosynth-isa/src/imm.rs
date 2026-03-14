/// Error returned when an immediate value is out of range for its type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ImmOutOfRange;

impl core::fmt::Display for ImmOutOfRange {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "immediate value out of range")
    }
}

/// Implement `TryFrom` for a list of integer types, with an inline range check.
macro_rules! impl_try_from {
    ($name:ident, $storage:ty, $min:expr, $max:expr, $($src:ty),+) => {
        $(
            impl TryFrom<$src> for $name {
                type Error = ImmOutOfRange;

                fn try_from(val: $src) -> Result<Self, Self::Error> {
                    let val = val as i64;
                    if val < $min || val > $max {
                        Err(ImmOutOfRange)
                    } else {
                        Ok(Self(val as $storage))
                    }
                }
            }
        )+
    };
}

/// 12-bit unsigned immediate (0–4095).
///
/// Used by ARM64 ADD/SUB immediate instructions and as the raw
/// (pre-scale) offset field in load/store unsigned-offset instructions.
///
/// # Examples
///
/// ```
/// use autosynth_isa::imm::{UImm12, ImmOutOfRange};
///
/// let imm = UImm12::try_from(100_i32).unwrap();
/// assert_eq!(imm.value(), 100);
///
/// assert!(UImm12::try_from(5000_i32).is_err());
/// assert!(UImm12::try_from(-1_i32).is_err());
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UImm12(u16);

impl UImm12 {
    pub const fn value(self) -> u16 {
        self.0
    }
}

impl_try_from!(UImm12, u16, 0, 4095, i8, u8, i16, u16, i32, u32, i64, u64, isize, usize);

/// 16-bit unsigned immediate (0–65535).
///
/// Used by ARM64 MOVZ/MOVK instructions.
///
/// # Examples
///
/// ```
/// use autosynth_isa::imm::{UImm16, ImmOutOfRange};
///
/// let imm = UImm16::try_from(42_u16).unwrap();
/// assert_eq!(imm.value(), 42);
///
/// assert!(UImm16::try_from(-1_i32).is_err());
/// assert!(UImm16::try_from(70000_i32).is_err());
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UImm16(u16);

impl UImm16 {
    pub const fn value(self) -> u16 {
        self.0
    }
}

impl From<u16> for UImm16 {
    fn from(val: u16) -> Self {
        Self(val)
    }
}

impl_try_from!(UImm16, u16, 0, 65535, i8, u8, i16, i32, u32, i64, u64, isize, usize);

/// 9-bit signed immediate (−256 to +255).
///
/// Used by ARM64 pre-index, post-index, and unscaled load/store instructions.
///
/// # Examples
///
/// ```
/// use autosynth_isa::imm::{SImm9, ImmOutOfRange};
///
/// let imm = SImm9::try_from(-16_i32).unwrap();
/// assert_eq!(imm.value(), -16);
/// assert_eq!(imm.bits(), (-16_i16 as u32) & 0x1FF);
///
/// assert!(SImm9::try_from(-257_i32).is_err());
/// assert!(SImm9::try_from(256_i32).is_err());
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SImm9(i16);

impl SImm9 {
    pub const fn value(self) -> i16 {
        self.0
    }

    /// Encode as the 9-bit field used in instructions.
    pub const fn bits(self) -> u32 {
        (self.0 as u32) & 0x1FF
    }
}

impl_try_from!(SImm9, i16, -256, 255, i8, u8, i16, u16, i32, u32, i64, u64, isize, usize);

/// 19-bit signed word offset (−262144 to +262143).
///
/// Used by ARM64 `B.cond` instructions. The offset is in words (4 bytes),
/// giving a ±1MB range.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SImm19(i32);

impl SImm19 {
    pub const fn value(self) -> i32 {
        self.0
    }

    pub const fn bits(self) -> u32 {
        (self.0 as u32) & 0x7FFFF
    }
}

impl_try_from!(SImm19, i32, -262144, 262143, i8, u8, i16, u16, i32, u32, i64, u64, isize, usize);

/// 26-bit signed word offset (−33554432 to +33554431).
///
/// Used by ARM64 `B` and `BL` instructions. The offset is in words (4 bytes),
/// giving a ±128MB range.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SImm26(i32);

impl SImm26 {
    pub const fn value(self) -> i32 {
        self.0
    }

    pub const fn bits(self) -> u32 {
        (self.0 as u32) & 0x03FF_FFFF
    }
}

impl_try_from!(SImm26, i32, -33554432, 33554431, i8, u8, i16, u16, i32, u32, i64, u64, isize, usize);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn uimm12_in_range() {
        assert_eq!(UImm12::try_from(0_i32).unwrap().value(), 0);
        assert_eq!(UImm12::try_from(4095_i64).unwrap().value(), 4095);
        assert_eq!(UImm12::try_from(100_u32).unwrap().value(), 100);
    }

    #[test]
    fn uimm12_out_of_range() {
        assert!(UImm12::try_from(4096_i32).is_err());
        assert!(UImm12::try_from(-1_i32).is_err());
        assert!(UImm12::try_from(70000_i64).is_err());
    }

    #[test]
    fn uimm16_in_range() {
        assert_eq!(UImm16::try_from(0_i32).unwrap().value(), 0);
        assert_eq!(UImm16::try_from(65535_u32).unwrap().value(), 65535);
        assert_eq!(UImm16::try_from(42_u16).unwrap().value(), 42);
    }

    #[test]
    fn uimm16_out_of_range() {
        assert!(UImm16::try_from(-1_i32).is_err());
        assert!(UImm16::try_from(70000_i64).is_err());
    }

    #[test]
    fn simm9_in_range() {
        assert_eq!(SImm9::try_from(-256_i32).unwrap().value(), -256);
        assert_eq!(SImm9::try_from(255_i32).unwrap().value(), 255);
        assert_eq!(SImm9::try_from(0_i64).unwrap().value(), 0);
    }

    #[test]
    fn simm9_out_of_range() {
        assert!(SImm9::try_from(-257_i32).is_err());
        assert!(SImm9::try_from(256_i32).is_err());
    }

    #[test]
    fn simm9_bits() {
        let imm = SImm9::try_from(-16_i32).unwrap();
        assert_eq!(imm.bits(), (-16_i32 as u32) & 0x1FF);
    }
}
