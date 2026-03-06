/// Register identity (x0-x31) for RISC-V 64-bit.
///
/// RISC-V has 32 general-purpose registers. Unlike aarch64, there are
/// no width-typed variants -- the instruction itself determines the
/// operation width (e.g. ADD vs ADDW).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum GprId {
    X0 = 0,
    X1 = 1,
    X2 = 2,
    X3 = 3,
    X4 = 4,
    X5 = 5,
    X6 = 6,
    X7 = 7,
    X8 = 8,
    X9 = 9,
    X10 = 10,
    X11 = 11,
    X12 = 12,
    X13 = 13,
    X14 = 14,
    X15 = 15,
    X16 = 16,
    X17 = 17,
    X18 = 18,
    X19 = 19,
    X20 = 20,
    X21 = 21,
    X22 = 22,
    X23 = 23,
    X24 = 24,
    X25 = 25,
    X26 = 26,
    X27 = 27,
    X28 = 28,
    X29 = 29,
    X30 = 30,
    X31 = 31,
}

impl GprId {
    /// 5-bit encoding index (0-31).
    pub const fn index(self) -> u8 {
        self as u8
    }

    /// Decode from a 5-bit register field.
    ///
    /// # Panics
    ///
    /// Panics if `index > 31`.
    pub const fn from_index(index: u8) -> Self {
        assert!(index < 32, "GprId index must be 0-31");
        // Safety: repr(u8) with variants 0..=31, and we checked index < 32.
        unsafe { core::mem::transmute(index) }
    }

    /// ABI name for this register.
    pub const fn abi_name(self) -> &'static str {
        match self {
            GprId::X0 => "zero",
            GprId::X1 => "ra",
            GprId::X2 => "sp",
            GprId::X3 => "gp",
            GprId::X4 => "tp",
            GprId::X5 => "t0",
            GprId::X6 => "t1",
            GprId::X7 => "t2",
            GprId::X8 => "s0",
            GprId::X9 => "s1",
            GprId::X10 => "a0",
            GprId::X11 => "a1",
            GprId::X12 => "a2",
            GprId::X13 => "a3",
            GprId::X14 => "a4",
            GprId::X15 => "a5",
            GprId::X16 => "a6",
            GprId::X17 => "a7",
            GprId::X18 => "s2",
            GprId::X19 => "s3",
            GprId::X20 => "s4",
            GprId::X21 => "s5",
            GprId::X22 => "s6",
            GprId::X23 => "s7",
            GprId::X24 => "s8",
            GprId::X25 => "s9",
            GprId::X26 => "s10",
            GprId::X27 => "s11",
            GprId::X28 => "t3",
            GprId::X29 => "t4",
            GprId::X30 => "t5",
            GprId::X31 => "t6",
        }
    }
}

/// A general-purpose register (x0-x31).
///
/// RISC-V always operates on 64-bit registers in RV64I. Width is
/// determined by the instruction (ADD vs ADDW), not the register.
/// Display uses ABI names by default.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Gpr(pub GprId);

impl Gpr {
    pub const ZERO: Self = Gpr(GprId::X0);
    pub const RA: Self = Gpr(GprId::X1);
    pub const SP: Self = Gpr(GprId::X2);
    pub const GP: Self = Gpr(GprId::X3);
    pub const TP: Self = Gpr(GprId::X4);
    pub const T0: Self = Gpr(GprId::X5);
    pub const T1: Self = Gpr(GprId::X6);
    pub const T2: Self = Gpr(GprId::X7);
    pub const S0: Self = Gpr(GprId::X8);
    pub const FP: Self = Gpr(GprId::X8);
    pub const S1: Self = Gpr(GprId::X9);
    pub const A0: Self = Gpr(GprId::X10);
    pub const A1: Self = Gpr(GprId::X11);
    pub const A2: Self = Gpr(GprId::X12);
    pub const A3: Self = Gpr(GprId::X13);
    pub const A4: Self = Gpr(GprId::X14);
    pub const A5: Self = Gpr(GprId::X15);
    pub const A6: Self = Gpr(GprId::X16);
    pub const A7: Self = Gpr(GprId::X17);
    pub const S2: Self = Gpr(GprId::X18);
    pub const S3: Self = Gpr(GprId::X19);
    pub const S4: Self = Gpr(GprId::X20);
    pub const S5: Self = Gpr(GprId::X21);
    pub const S6: Self = Gpr(GprId::X22);
    pub const S7: Self = Gpr(GprId::X23);
    pub const S8: Self = Gpr(GprId::X24);
    pub const S9: Self = Gpr(GprId::X25);
    pub const S10: Self = Gpr(GprId::X26);
    pub const S11: Self = Gpr(GprId::X27);
    pub const T3: Self = Gpr(GprId::X28);
    pub const T4: Self = Gpr(GprId::X29);
    pub const T5: Self = Gpr(GprId::X30);
    pub const T6: Self = Gpr(GprId::X31);

    /// 5-bit encoding index (0-31).
    pub const fn index(self) -> u8 {
        self.0.index()
    }

    /// Format using raw register names (x0-x31).
    pub fn fmt_raw(self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "x{}", self.index())
    }

    /// Format using ABI register names (zero, ra, sp, a0-a7, etc.).
    pub fn fmt_abi(self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.0.abi_name())
    }
}

impl core::fmt::Display for Gpr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.fmt_abi(f)
    }
}
