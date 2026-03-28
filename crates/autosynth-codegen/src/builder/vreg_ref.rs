use autosynth_ir::VReg;

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

/// How a ref obtains its value.
#[derive(Debug, Clone)]
pub enum VRefSource {
    /// Single predecessor — just an alias.
    Direct(VRegOrRef),
    /// Merge point — multiple predecessors provide different values.
    Phi(Vec<VRegOrRef>),
}
