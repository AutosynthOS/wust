/// Error returned when an immediate value is out of range for its type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ImmOutOfRange;

impl core::fmt::Display for ImmOutOfRange {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "immediate value out of range")
    }
}

/// 12-bit signed immediate (-2048 to 2047).
///
/// Used by I-type instructions (ADDI, LW, LD, JALR) and S-type
/// instructions (SW, SD) for the offset field.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SImm12(i16);

impl SImm12 {
    pub const fn new(val: i16) -> Result<Self, ImmOutOfRange> {
        if val < -2048 || val > 2047 {
            Err(ImmOutOfRange)
        } else {
            Ok(SImm12(val))
        }
    }

    pub const fn value(self) -> i16 {
        self.0
    }

    /// Encode as the 12-bit field used in I-type instructions.
    pub const fn bits(self) -> u32 {
        (self.0 as u32) & 0xFFF
    }
}

/// 20-bit signed immediate for U-type instructions (LUI, AUIPC).
///
/// Represents the upper 20 bits of a 32-bit value. The value stored
/// is the raw 20-bit field (bits [31:12] of the target).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SImm20(i32);

impl SImm20 {
    pub const fn new(val: i32) -> Result<Self, ImmOutOfRange> {
        if val < -(1 << 19) || val > ((1 << 19) - 1) {
            Err(ImmOutOfRange)
        } else {
            Ok(SImm20(val))
        }
    }

    pub const fn value(self) -> i32 {
        self.0
    }

    /// Encode as the 20-bit field used in U-type instructions.
    pub const fn bits(self) -> u32 {
        (self.0 as u32) & 0xFFFFF
    }
}

/// 13-bit signed branch immediate, always even (2-byte aligned).
///
/// Used by B-type instructions (BEQ, BNE, BLT, BGE). The value
/// represents a byte offset from the branch instruction. Bit 0 is
/// always zero and is not encoded.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BImm13(i16);

impl BImm13 {
    pub const fn new(val: i16) -> Result<Self, ImmOutOfRange> {
        if val < -4096 || val > 4095 {
            Err(ImmOutOfRange)
        } else if (val & 1) != 0 {
            Err(ImmOutOfRange)
        } else {
            Ok(BImm13(val))
        }
    }

    pub const fn value(self) -> i16 {
        self.0
    }

    /// Encode into the B-type immediate bit positions.
    ///
    /// B-type layout: `imm[12|10:5] ... imm[4:1|11]`
    /// The raw signed value has bit 0 = 0 (2-byte aligned).
    pub const fn encode_b_type(self) -> u32 {
        let v = self.0 as u32;
        let bit12 = (v >> 12) & 1;
        let bits10_5 = (v >> 5) & 0x3F;
        let bits4_1 = (v >> 1) & 0xF;
        let bit11 = (v >> 11) & 1;
        (bit12 << 31) | (bits10_5 << 25) | (bits4_1 << 8) | (bit11 << 7)
    }
}

/// 21-bit signed jump immediate, always even (2-byte aligned).
///
/// Used by the J-type instruction (JAL). The value represents a byte
/// offset from the jump instruction. Bit 0 is always zero and is not
/// encoded.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct JImm21(i32);

impl JImm21 {
    pub const fn new(val: i32) -> Result<Self, ImmOutOfRange> {
        if val < -(1 << 20) || val > ((1 << 20) - 1) {
            Err(ImmOutOfRange)
        } else if (val & 1) != 0 {
            Err(ImmOutOfRange)
        } else {
            Ok(JImm21(val))
        }
    }

    pub const fn value(self) -> i32 {
        self.0
    }

    /// Encode into the J-type immediate bit positions.
    ///
    /// J-type layout: `imm[20|10:1|11|19:12]`
    /// The raw signed value has bit 0 = 0 (2-byte aligned).
    pub const fn encode_j_type(self) -> u32 {
        let v = self.0 as u32;
        let bit20 = (v >> 20) & 1;
        let bits10_1 = (v >> 1) & 0x3FF;
        let bit11 = (v >> 11) & 1;
        let bits19_12 = (v >> 12) & 0xFF;
        (bit20 << 31) | (bits10_1 << 21) | (bit11 << 20) | (bits19_12 << 12)
    }
}
