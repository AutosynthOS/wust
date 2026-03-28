use std::collections::BTreeMap;
use autosynth_ir::VReg;
use autosynth_regalloc::{RegAlloc, VRegRefDef};

/// Per-block wasm region state — named stacks of VRegs.
#[derive(Clone)]
pub struct WasmBlock {
    pub regions: BTreeMap<&'static str, Vec<VReg>>,
}

impl WasmBlock {
    /// Create a successor block by cloning this block's region state.
    pub fn fork(&self) -> WasmBlock {
        self.clone()
    }

    /// Merge another predecessor's state into this block.
    /// Slots that agree stay as-is. Slots that differ become Phi refs.
    pub fn merge(&mut self, other: &WasmBlock, regalloc: &mut RegAlloc) {
        for (name, slots) in self.regions.iter_mut() {
            let other_slots = &other.regions[name];
            for i in 0..slots.len() {
                if slots[i] != other_slots[i] {
                    let ref_def = VRegRefDef::Phi(vec![slots[i], other_slots[i]]);
                    slots[i] = VReg::Ref(regalloc.alloc_ref(ref_def));
                }
            }
        }
    }

    pub fn region(&mut self, name: &str) -> &mut Vec<VReg> {
        self.regions.get_mut(name).expect(name)
    }

    pub fn region_ref(&self, name: &str) -> &[VReg] {
        &self.regions[name]
    }
}
