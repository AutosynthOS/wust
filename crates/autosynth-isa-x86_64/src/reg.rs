/// Register identity (0-15) without width info.
///
/// This is the raw 4-bit index shared by 32-bit and 64-bit forms.
/// Use `Gpr32` or `Gpr64` to attach a width.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum GprId {
    Rax = 0,
    Rcx = 1,
    Rdx = 2,
    Rbx = 3,
    Rsp = 4,
    Rbp = 5,
    Rsi = 6,
    Rdi = 7,
    R8 = 8,
    R9 = 9,
    R10 = 10,
    R11 = 11,
    R12 = 12,
    R13 = 13,
    R14 = 14,
    R15 = 15,
}

impl GprId {
    /// 4-bit encoding index (0-15).
    pub const fn index(self) -> u8 {
        self as u8
    }

    /// Low 3 bits of the register encoding.
    pub const fn low3(self) -> u8 {
        self.index() & 0x07
    }

    /// Whether this register requires the REX.B or REX.R extension bit.
    pub const fn is_extended(self) -> bool {
        self.index() >= 8
    }

    /// Decode from a 4-bit register field.
    ///
    /// # Panics
    ///
    /// Panics if `index > 15`.
    pub const fn from_index(index: u8) -> Self {
        assert!(index < 16, "GprId index must be 0-15");
        // Safety: repr(u8) with variants 0..=15, and we checked index < 16.
        unsafe { core::mem::transmute(index) }
    }
}

/// 32-bit GPR (`eax`-`r15d`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Gpr32(pub GprId);

/// 64-bit GPR (`rax`-`r15`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Gpr64(pub GprId);

macro_rules! gpr_constants {
    ($ty:ident) => {
        impl $ty {
            pub const RAX: Self = $ty(GprId::Rax);
            pub const RCX: Self = $ty(GprId::Rcx);
            pub const RDX: Self = $ty(GprId::Rdx);
            pub const RBX: Self = $ty(GprId::Rbx);
            pub const RSP: Self = $ty(GprId::Rsp);
            pub const RBP: Self = $ty(GprId::Rbp);
            pub const RSI: Self = $ty(GprId::Rsi);
            pub const RDI: Self = $ty(GprId::Rdi);
            pub const R8: Self = $ty(GprId::R8);
            pub const R9: Self = $ty(GprId::R9);
            pub const R10: Self = $ty(GprId::R10);
            pub const R11: Self = $ty(GprId::R11);
            pub const R12: Self = $ty(GprId::R12);
            pub const R13: Self = $ty(GprId::R13);
            pub const R14: Self = $ty(GprId::R14);
            pub const R15: Self = $ty(GprId::R15);

            pub const fn id(self) -> GprId {
                self.0
            }

            pub const fn index(self) -> u8 {
                self.0.index()
            }

            pub const fn low3(self) -> u8 {
                self.0.low3()
            }

            pub const fn is_extended(self) -> bool {
                self.0.is_extended()
            }
        }
    };
}

gpr_constants!(Gpr32);
gpr_constants!(Gpr64);

/// GPR at either width.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Gpr {
    R32(Gpr32),
    R64(Gpr64),
}

impl Gpr {
    /// 4-bit encoding index (0-15).
    pub const fn index(self) -> u8 {
        match self {
            Gpr::R32(r) => r.index(),
            Gpr::R64(r) => r.index(),
        }
    }

    /// Low 3 bits of the register encoding.
    pub const fn low3(self) -> u8 {
        self.index() & 0x07
    }

    /// Whether this register requires REX extension.
    pub const fn is_extended(self) -> bool {
        self.index() >= 8
    }

    /// Whether this is a 64-bit register.
    pub const fn is_64(self) -> bool {
        matches!(self, Gpr::R64(_))
    }

    /// Byte size: 4 for R32, 8 for R64.
    pub const fn byte_size(self) -> u8 {
        match self {
            Gpr::R32(_) => 4,
            Gpr::R64(_) => 8,
        }
    }
}

impl From<Gpr32> for Gpr {
    fn from(r: Gpr32) -> Self {
        Gpr::R32(r)
    }
}

impl From<Gpr64> for Gpr {
    fn from(r: Gpr64) -> Self {
        Gpr::R64(r)
    }
}

const GPR32_NAMES: [&str; 16] = [
    "eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi",
    "r8d", "r9d", "r10d", "r11d", "r12d", "r13d", "r14d", "r15d",
];

const GPR64_NAMES: [&str; 16] = [
    "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi",
    "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15",
];

impl core::fmt::Display for Gpr32 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", GPR32_NAMES[self.index() as usize])
    }
}

impl core::fmt::Display for Gpr64 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", GPR64_NAMES[self.index() as usize])
    }
}

impl core::fmt::Display for Gpr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Gpr::R32(r) => write!(f, "{r}"),
            Gpr::R64(r) => write!(f, "{r}"),
        }
    }
}
