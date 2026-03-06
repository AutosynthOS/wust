#![no_std]

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
