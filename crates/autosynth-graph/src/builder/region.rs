//! Stack region — tracks VRegRefKeys at managed stack positions.
//! Also defines VRegRef and VRegRefKey.
use autosynth_isa::{PReg, Width};
use smallvec::SmallVec;

use crate::{Input, MemSlot, Operation, VCode, builder::state::SharedBuildState};

/// A contiguous region on the managed stack (locals, operands, fibre).
///
/// Tracks VRegRefKeys at each slot position. The region computes
/// MemSlots from its base + offset for memory-backed operations.
#[derive(Debug, Clone)]
pub(crate) struct BuilderRegion {
    base: PReg,
    offset: u16,
    cursor: u16,
    entries: Vec<MemEntry>,
    state: SharedBuildState,
}

#[derive(Debug, Clone)]
struct MemEntry {
    width: Width,
    value: Input,
}

impl BuilderRegion {
    pub fn new(base: PReg, base_offset: u16, state: &SharedBuildState) -> Self {
        Self {
            base,
            offset: base_offset,
            cursor: 0,
            entries: Vec::new(),
            state: state.clone(),
        }
    }

    fn mem_slot_at_cursor(&self) -> MemSlot {
        MemSlot {
            base: self.base,
            offset: self.offset as u32 + self.cursor as u32,
        }
    }

    fn width(&self, value: &Input) -> Width {
        self.state
            .borrow()
            .width(self.state.borrow().unwrap_as_def_key(&value))
    }

    pub fn push(&mut self, value: Input) -> Operation {
        let mem_slot = self.mem_slot_at_cursor();
        let width = self.width(&value);
        self.entries.push(MemEntry {
            width,
            value: value.clone(),
        });
        self.cursor += width.bytes() as u16;
        Operation {
            opcode: VCode::SetSlot(mem_slot),
            inputs: smallvec::smallvec![value],
            effect: None,
            prev: None,
            defines: SmallVec::new(),
        }
    }

    pub fn get_index(&self, index: usize) -> (Input, Width) {
        let entry = &self.entries[index];
        (entry.value.clone(), entry.width)
    }

    pub fn set_index_expect_width(&mut self, index: usize, value: Input, expected_width: Width) -> Operation {
        assert_eq!(self.entries[index].width, expected_width);
        let mem = self.mem_slot_at_index(index);
        self.entries[index].value = value.clone();
        Operation {
            opcode: VCode::SetSlot(mem),
            inputs: smallvec::smallvec![value],
            defines: SmallVec::new(),
            effect: None,
            prev: None,
        }
    }

    fn mem_slot_at_index(&self, index: usize) -> MemSlot {
        MemSlot {
            base: self.base,
            offset: self.offset as u32 + (index as u32 * 4), // TODO: use actual entry widths
        }
    }

    pub fn convert_vregs_to_vrefs(&mut self) {
        for entry in &mut self.entries {
            if let Input::VReg(vreg_key) = &entry.value {
                entry.value = self.state.borrow_mut().define_ref(*vreg_key);
            }
        }
    }

    pub fn pop(&mut self) -> (Operation, Input, Width) {
        let entry = self.entries.pop().unwrap();
        self.cursor -= entry.width.bytes() as u16;
        (
            Operation {
                opcode: VCode::ClearSlot(self.mem_slot_at_cursor()),
                inputs: smallvec::smallvec![entry.value.clone()],
                defines: SmallVec::new(),
                effect: None,
                prev: None,
            },
            entry.value,
            entry.width,
        )
    }
}
