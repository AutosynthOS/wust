//! VRegAllocator — global VReg factory.

use alloc::rc::Rc;
use alloc::vec::Vec;
use autosynth_ir::{VReg, VRegState};
use autosynth_isa::{PReg, Width};
use core::cell::RefCell;

pub type SharedVRegAllocator = Rc<RefCell<VRegAllocator>>;

/// Global VReg factory — hands out VReg IDs and stores state.
#[derive(Debug, Clone)]
pub struct VRegAllocator {
    states: Vec<VRegState>,
}

impl VRegAllocator {
    pub fn new() -> Self {
        Self { states: Vec::new() }
    }

    pub fn define(&mut self, state: VRegState) -> VReg {
        let id = VReg(self.states.len() as u32);
        self.states.push(state);
        id
    }

    pub fn set_target(&mut self, id: VReg, preg: PReg) {
        self.states[id.0 as usize].target = Some(preg);
    }

    pub fn state(&self, id: VReg) -> &VRegState {
        &self.states[id.0 as usize]
    }
    pub fn state_mut(&mut self, id: VReg) -> &mut VRegState {
        &mut self.states[id.0 as usize]
    }
    pub fn width(&self, id: VReg) -> Width {
        self.states[id.0 as usize].width
    }
    pub fn len(&self) -> usize {
        self.states.len()
    }
}
