//! VRegState — per-VReg mutable live state.

use autosynth_isa::{PReg, Width};

/// A memory slot on the managed stack.
#[derive(Debug, Clone, Copy)]
pub struct MemSlot {
    pub base: PReg,
    pub offset: u32,
    pub dirty: bool,
}

/// Per-block mutable live state for a VReg.
///
/// Multiple fields can be active simultaneously — a value can be
/// in a register AND in memory AND known as a constant.
#[derive(Debug, Clone)]
pub struct VRegState {
    pub preg: Option<PReg>,
    pub slot: Option<MemSlot>,
    pub known_const: Option<i64>,
    pub width: Width,
}

impl VRegState {
    pub fn new(width: Width) -> Self {
        Self {
            preg: None,
            slot: None,
            known_const: None,
            width,
        }
    }
}
