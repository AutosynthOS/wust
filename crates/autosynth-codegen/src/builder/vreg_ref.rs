use autosynth_ir::{VCode, VReg};

/// A value during building — either a concrete VReg or an indirection
/// (ref) for block-inherited values. Resolved at build() time.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VRegOrRef {
    VReg(VReg),
    Ref(VRefId),
}

/// Index into the function builder's ref table.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VRefId(pub u32);

impl From<VReg> for VRegOrRef {
    fn from(vreg: VReg) -> Self {
        VRegOrRef::VReg(vreg)
    }
}

/// An item in the builder's stream — either an operand (resolved
/// later) or a VCode instruction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BuilderItem {
    Operand(VRegOrRef),
    Inst(VCode),
}
