use std::cell::RefCell;
use std::rc::Weak;

use autosynth_codegen::builder::VRegOrRef;
use autosynth_ir::{SlotRef, VReg, VRegState};
use autosynth_isa::PReg;
use autosynth_regalloc::VRegAllocator;

/// A region on the managed stack (locals, operands, fibre).
/// Tracks VRegs and their individual slot offsets.
/// Holds a weak ref to the allocator for width lookups.
#[derive(Clone)]
pub struct StackRegion {
    pub base: PReg,
    pub base_offset: u32,
    pub cursor: u32,
    entries: Vec<VRegOrRef>,
    alloc: Weak<RefCell<VRegAllocator>>,
}

impl StackRegion {
    pub fn new(base: PReg, base_offset: u32, alloc: &std::rc::Rc<RefCell<VRegAllocator>>) -> Self {
        Self {
            base,
            base_offset,
            cursor: 0,
            entries: Vec::new(),
            alloc: std::rc::Rc::downgrade(alloc),
        }
    }

    /// Push a VReg onto the region. Slot offset computed from VReg's width.
    /// Caller must emit a VCode::SetSlot operation
    pub fn push(&mut self, val: VRegOrRef) -> SlotRef {
        let byte_size = self.vreg_bytes(val);
        let slot = SlotRef {
            base: self.base,
            offset: self.base_offset + self.cursor,
        };
        self.cursor += byte_size;
        self.entries.push(val);
        slot
    }

    /// Define a new VReg, assign it a stack slot, push it onto the region.
    /// `dirty`: true if the register value is newer than the stack value.
    pub fn push_define(&mut self, mut state: VRegState) -> VReg {
        state.slot = Some(SlotRef {
            base: self.base,
            offset: self.base_offset + self.cursor,
        });
        self.cursor += state.width.bytes();
        let alloc = self.alloc.upgrade().expect("allocator dropped");
        let vreg = alloc.borrow_mut().define(state);
        self.entries.push(VRegOrRef::VReg(vreg));
        vreg
    }

    pub fn pop(&mut self) -> Option<VRegOrRef> {
        self.entries.pop()
    }

    pub fn get(&self, idx: usize) -> &VRegOrRef {
        &self.entries[idx]
    }

    pub fn set_val(&mut self, idx: usize, val: VRegOrRef) {
        self.entries[idx] = val;
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn entries_mut(&mut self) -> &mut [VRegOrRef] {
        &mut self.entries
    }

    pub fn size(&self) -> u32 {
        self.cursor
    }

    fn vreg_bytes(&self, val: VRegOrRef) -> u32 {
        let alloc = self.alloc.upgrade().expect("allocator dropped");
        let alloc = alloc.borrow();
        match val {
            VRegOrRef::VReg(vreg) => alloc.width(vreg).bytes(),
            VRegOrRef::Ref(_) => todo!("ref width lookup"),
        }
    }
}
