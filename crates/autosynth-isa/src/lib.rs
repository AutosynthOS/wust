#![no_std]

pub mod imm;

pub use imm::{ImmOutOfRange, SImm9, UImm12, UImm16};

/// Error returned when the encode buffer is too small.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EncodeError;

impl core::fmt::Display for EncodeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "encode buffer too small")
    }
}

/// A machine instruction that can be encoded to bytes.
pub trait Instruction: Sized {
    /// Safe encode into a byte slice.
    fn encode(&self, buf: &mut [u8]) -> Result<usize, EncodeError>;
}

/// Access width for loads, stores, and other memory operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Width {
    W32,
    W64,
}

impl Width {
    /// Size in bytes.
    pub const fn bytes(self) -> u32 {
        match self {
            Width::W32 => 4,
            Width::W64 => 8,
        }
    }
}

impl core::fmt::Display for Width {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Width::W32 => write!(f, "w32"),
            Width::W64 => write!(f, "w64"),
        }
    }
}

/// Physical register identifier.
///
/// Architecture-neutral — just an index. The backend maps this to
/// concrete hardware registers (e.g. `x9` on ARM64, `rax` on x86).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PReg(pub u8);

/// Architecture-abstract register role, resolved to a physical register
/// by the backend's [`MachineConfig`](super::MachineConfig).
///
/// Lets the frontend declare named registers (frame pointer, fuel counter,
/// etc.) without knowing the target platform's register numbering.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IsaReg {
    /// The platform's frame pointer register (e.g. x29 on aarch64).
    FramePointer,
    /// The platform's stack pointer register (e.g. x28 as software SP on aarch64).
    StackPointer,
    /// The platform's return address / link register (e.g. x30 on aarch64).
    ReturnAddress,
    /// A general-purpose 64-bit register, auto-allocated from the remaining pool.
    /// Positive indexes allocate from the start (0, 1, 2...),
    /// negative indexes allocate from the end (-1, -2, -3...).
    Alloc64(i8),
}

/// Result of trying to fold an operand as an immediate.
///
/// The backend pattern-matches on this to select between immediate
/// and register instruction forms.
///
/// # Examples
///
/// ```
/// use autosynth_isa::{PRegOr, PReg};
///
/// let folded: PRegOr<u16> = PRegOr::Imm(42);
/// let not_folded: PRegOr<u16> = PRegOr::PReg(PReg(9));
///
/// match folded {
///     PRegOr::Imm(val) => assert_eq!(val, 42),
///     PRegOr::PReg(_) => panic!("expected immediate"),
/// }
/// ```
#[derive(Debug, Clone, Copy)]
pub enum PRegOr<T> {
    /// The operand was folded into an immediate value.
    Imm(T),
    /// The operand is in a physical register.
    PReg(PReg),
}
