/// Register identity (R0–R30) without width info.
///
/// This is the raw 5-bit index shared by W and X forms.
/// Use `WGpr` or `XGpr` to attach a width.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum GprId {
    R0 = 0,
    R1,
    R2,
    R3,
    R4,
    R5,
    R6,
    R7,
    R8,
    R9,
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,
    R16,
    R17,
    R18,
    R19,
    R20,
    R21,
    R22,
    R23,
    R24,
    R25,
    R26,
    R27,
    R28,
    R29,
    R30,
}

impl GprId {
    pub const LINK_REGISTER: GprId = GprId::R30;

    /// 5-bit encoding index (0–30).
    pub const fn index(self) -> u8 {
        self as u8
    }

    /// Decode from a 5-bit register field.
    ///
    /// # Panics
    ///
    /// Panics if `index > 30`.
    pub const fn from_index(index: u8) -> Self {
        assert!(index < 31, "GprId index must be 0-30");
        // Safety: repr(u8) with variants 0..=30, and we checked index < 31.
        unsafe { core::mem::transmute(index) }
    }
}

/// 32-bit GPR (`w0`–`w30`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct WGpr(pub GprId);

/// 64-bit GPR (`x0`–`x30`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct XGpr(pub GprId);

macro_rules! gpr_constants {
    ($ty:ident) => {
        impl $ty {
            pub const R0: Self = $ty(GprId::R0);
            pub const R1: Self = $ty(GprId::R1);
            pub const R2: Self = $ty(GprId::R2);
            pub const R3: Self = $ty(GprId::R3);
            pub const R4: Self = $ty(GprId::R4);
            pub const R5: Self = $ty(GprId::R5);
            pub const R6: Self = $ty(GprId::R6);
            pub const R7: Self = $ty(GprId::R7);
            pub const R8: Self = $ty(GprId::R8);
            pub const R9: Self = $ty(GprId::R9);
            pub const R10: Self = $ty(GprId::R10);
            pub const R11: Self = $ty(GprId::R11);
            pub const R12: Self = $ty(GprId::R12);
            pub const R13: Self = $ty(GprId::R13);
            pub const R14: Self = $ty(GprId::R14);
            pub const R15: Self = $ty(GprId::R15);
            pub const R16: Self = $ty(GprId::R16);
            pub const R17: Self = $ty(GprId::R17);
            pub const R18: Self = $ty(GprId::R18);
            pub const R19: Self = $ty(GprId::R19);
            pub const R20: Self = $ty(GprId::R20);
            pub const R21: Self = $ty(GprId::R21);
            pub const R22: Self = $ty(GprId::R22);
            pub const R23: Self = $ty(GprId::R23);
            pub const R24: Self = $ty(GprId::R24);
            pub const R25: Self = $ty(GprId::R25);
            pub const R26: Self = $ty(GprId::R26);
            pub const R27: Self = $ty(GprId::R27);
            pub const R28: Self = $ty(GprId::R28);
            pub const R29: Self = $ty(GprId::R29);
            pub const R30: Self = $ty(GprId::R30);

            pub const fn index(self) -> u8 {
                self.0.index()
            }
        }
    };
}

gpr_constants!(WGpr);
gpr_constants!(XGpr);

/// GPR at either width.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Gpr {
    W(WGpr),
    X(XGpr),
}

impl Gpr {
    /// 5-bit encoding index (0–30).
    pub const fn index(self) -> u8 {
        match self {
            Gpr::W(w) => w.index(),
            Gpr::X(x) => x.index(),
        }
    }

    /// The `sf` bit: 0 for W, 1 for X.
    pub const fn sf(self) -> u32 {
        match self {
            Gpr::W(_) => 0,
            Gpr::X(_) => 1,
        }
    }

    /// Load/store size bits: `0b10` for W, `0b11` for X.
    pub const fn ls_size(self) -> u32 {
        match self {
            Gpr::W(_) => 0b10,
            Gpr::X(_) => 0b11,
        }
    }

    /// Byte size: 4 for W, 8 for X.
    pub const fn byte_size(self) -> u8 {
        match self {
            Gpr::W(_) => 4,
            Gpr::X(_) => 8,
        }
    }

    pub(crate) fn fmt_reg(self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Gpr::W(w) => write!(f, "w{}", w.index()),
            Gpr::X(x) => write!(f, "x{}", x.index()),
        }
    }
}

impl From<WGpr> for Gpr {
    fn from(w: WGpr) -> Self {
        Gpr::W(w)
    }
}

impl From<XGpr> for Gpr {
    fn from(x: XGpr) -> Self {
        Gpr::X(x)
    }
}

/// GPR or zero register — used in most ALU and load/store data positions.
///
/// Register 31 means ZR. Width is carried by the variant.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GprOrZr {
    Gpr(Gpr),
    /// 32-bit zero register.
    Wzr,
    /// 64-bit zero register.
    Xzr,
}

impl GprOrZr {
    /// 5-bit encoding index (0–30 for GPRs, 31 for ZR).
    pub const fn index(self) -> u8 {
        match self {
            GprOrZr::Gpr(g) => g.index(),
            GprOrZr::Wzr | GprOrZr::Xzr => 31,
        }
    }

    /// The `sf` bit: 0 for 32-bit, 1 for 64-bit.
    pub const fn sf(self) -> u32 {
        match self {
            GprOrZr::Gpr(g) => g.sf(),
            GprOrZr::Wzr => 0,
            GprOrZr::Xzr => 1,
        }
    }

    /// Load/store size bits: `0b10` for 32-bit, `0b11` for 64-bit.
    pub const fn ls_size(self) -> u32 {
        match self {
            GprOrZr::Gpr(g) => g.ls_size(),
            GprOrZr::Wzr => 0b10,
            GprOrZr::Xzr => 0b11,
        }
    }

    /// Byte size: 4 for 32-bit, 8 for 64-bit.
    pub const fn byte_size(self) -> u8 {
        match self {
            GprOrZr::Gpr(g) => g.byte_size(),
            GprOrZr::Wzr => 4,
            GprOrZr::Xzr => 8,
        }
    }

    pub(crate) fn fmt_reg(self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            GprOrZr::Gpr(g) => g.fmt_reg(f),
            GprOrZr::Wzr => write!(f, "wzr"),
            GprOrZr::Xzr => write!(f, "xzr"),
        }
    }
}

impl From<WGpr> for GprOrZr {
    fn from(w: WGpr) -> Self {
        GprOrZr::Gpr(Gpr::W(w))
    }
}

impl From<XGpr> for GprOrZr {
    fn from(x: XGpr) -> Self {
        GprOrZr::Gpr(Gpr::X(x))
    }
}

impl From<Gpr> for GprOrZr {
    fn from(g: Gpr) -> Self {
        GprOrZr::Gpr(g)
    }
}

/// GPR or stack pointer — used in add/sub immediate Rd/Rn and
/// load/store base register positions.
///
/// Register 31 means SP. SP is always displayed as `sp`.
/// Width comes from the `Gpr` variant; SP defaults to 64-bit.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GprOrSp {
    Gpr(Gpr),
    Sp,
}

impl GprOrSp {
    pub const STACK_POINTER_IDX: u8 = 31;

    /// 5-bit encoding index (0–30 for GPRs, 31 for SP).
    pub const fn index(self) -> u8 {
        match self {
            GprOrSp::Gpr(g) => g.index(),
            GprOrSp::Sp => GprOrSp::STACK_POINTER_IDX,
        }
    }

    /// The `sf` bit. SP defaults to 1 (64-bit).
    pub const fn sf(self) -> u32 {
        match self {
            GprOrSp::Gpr(g) => g.sf(),
            GprOrSp::Sp => 1,
        }
    }

    /// Format using the register's own width (`w0`/`x0`/`sp`).
    pub(crate) fn fmt_reg(self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            GprOrSp::Gpr(g) => g.fmt_reg(f),
            GprOrSp::Sp => write!(f, "sp"),
        }
    }

    /// Format as a 64-bit base register (always `x`-prefix / `sp`).
    pub(crate) fn fmt_base(self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            GprOrSp::Gpr(g) => write!(f, "x{}", g.index()),
            GprOrSp::Sp => write!(f, "sp"),
        }
    }
}

impl From<WGpr> for GprOrSp {
    fn from(w: WGpr) -> Self {
        GprOrSp::Gpr(Gpr::W(w))
    }
}

impl From<XGpr> for GprOrSp {
    fn from(x: XGpr) -> Self {
        GprOrSp::Gpr(Gpr::X(x))
    }
}

impl From<Gpr> for GprOrSp {
    fn from(g: Gpr) -> Self {
        GprOrSp::Gpr(g)
    }
}
