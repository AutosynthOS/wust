//! SharedBuildState — shared arena for vregs and vreg refs.

use std::cell::RefCell;
use std::rc::Rc;

use autosynth_isa::Width;
use slotmap::SlotMap;

use crate::{
    Input, OpKey, Operation, VInit, VRegKey,
    types::VRegRefKey,
};

/// Shared mutable state for the builder.
///
/// All regions and blocks allocate VRegs and VRegRefs through this.
#[derive(Debug)]
pub struct BuildState {
    pub vreg_defs: SlotMap<VRegKey, VInit>,
    pub vreg_refs: SlotMap<VRegRefKey, VRegKey>,
    pub operations: SlotMap<OpKey, Operation>,
}

pub type SharedBuildState = Rc<RefCell<BuildState>>;

impl BuildState {
    pub fn new() -> Self {
        Self {
            vreg_defs: SlotMap::with_key(),
            vreg_refs: SlotMap::with_key(),
            operations: SlotMap::with_key(),
        }
    }

    pub fn define(&mut self, init: VInit) -> Input {
        Input::VReg(self.vreg_defs.insert(init))
    }

    pub fn define_ref(&mut self, vreg_key: VRegKey) -> Input {
        let vreg_ref_key = self.vreg_refs.insert(vreg_key);
        Input::VRef(vreg_ref_key)
    }

    pub fn unwrap_as_def_key(&self, ref_key: &Input) -> VRegKey {
        match ref_key {
            Input::VRef(vreg_ref_key) => self.vreg_refs.get(*vreg_ref_key).copied().unwrap(),
            Input::VReg(vreg_key) => *vreg_key,
            _ => panic!("unwrap_as_def called on non-def vreg_ref"),
        }
    }

    pub fn width(&self, vreg_key: VRegKey) -> Width {
        self.vreg_defs.get(vreg_key).expect("missing vreg_key").width
    }
}
