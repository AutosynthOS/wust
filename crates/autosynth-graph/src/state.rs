use autosynth_isa::{PReg, Width};
use crate::op::Op;
use crate::VRegRef;

/// Memory slot on the managed stack.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SlotRef {
    pub base: PReg,
    pub offset: u32,
}

/// The full state of a value. Identity is structural — two VRegStates
/// with identical fields are the same value.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VRegState {
    pub width: Width,
    pub preg: Option<PReg>,
    pub target: Option<PReg>,
    pub slot: Option<SlotRef>,
    pub dirty: bool,
    pub r#const: Option<i64>,
    pub op: Option<Op>,
}

impl VRegState {
    pub fn new(width: Width) -> Self {
        Self {
            width,
            preg: None,
            target: None,
            slot: None,
            dirty: false,
            r#const: None,
            op: None,
        }
    }
}
