use autosynth_isa::{PReg, Width};
use crate::node::NodeRef;
use crate::op::Op;

/// Memory slot on the managed stack.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SlotRef {
    pub base: PReg,
    pub offset: u32,
}

/// Identity anchor for a value.
///
/// Every VRegState traces back to a root definition. Operations that
/// don't change the underlying value (SetSlot, ClearSlot, assign_preg)
/// are just views — they reference the original via `Ref(source)`.
///
/// Operations that produce NEW values (params, consts, ALU ops, call
/// results) are `Root` — they ARE the definition.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Define {
    /// This is the original definition of a value.
    Root,
    /// This is a view of another value (same value, different metadata).
    Ref(NodeRef),
}

/// The full state of a value. Identity is structural — two VRegStates
/// with identical fields are the same value.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VRegState {
    pub width: Width,
    pub define: Define,
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
            define: Define::Root,
            preg: None,
            target: None,
            slot: None,
            dirty: false,
            r#const: None,
            op: None,
        }
    }
}
