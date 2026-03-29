//! VRegAllocator — global VReg factory.

use alloc::rc::Rc;
use alloc::vec::Vec;
use autosynth_ir::{VInit, VReg};
use autosynth_isa::{PReg, Width};
use core::cell::RefCell;

/// Immutable metadata for a defined virtual register.
#[derive(Debug, Clone)]
pub struct VRegDef {
    pub id: VReg,
    pub width: Width,
    pub init: VInit,
    pub target: Option<PReg>,
}

/// Global VReg factory — hands out VReg IDs and stores definitions.
#[derive(Debug, Clone)]
pub struct VRegAllocator {
    defs: Vec<VRegDef>,
}

impl VRegAllocator {
    pub fn new() -> Self {
        Self { defs: Vec::new() }
    }

    pub fn define(&mut self, init: VInit, width: Width) -> VReg {
        let id = VReg(self.defs.len() as u32);
        let target = match &init {
            VInit::PReg(preg) => Some(*preg),
            _ => None,
        };
        self.defs.push(VRegDef { id, width, init, target });
        id
    }

    pub fn set_target(&mut self, id: VReg, preg: PReg) {
        self.defs[id.0 as usize].target = Some(preg);
    }

    pub fn def(&self, id: VReg) -> &VRegDef { &self.defs[id.0 as usize] }
    pub fn def_mut(&mut self, id: VReg) -> &mut VRegDef { &mut self.defs[id.0 as usize] }
    pub fn init(&self, id: VReg) -> &VInit { &self.defs[id.0 as usize].init }
    pub fn width(&self, id: VReg) -> Width { self.defs[id.0 as usize].width }
    pub fn len(&self) -> usize { self.defs.len() }
}

pub type SharedVRegAllocator = Rc<RefCell<VRegAllocator>>;
