use std::collections::BTreeMap;
use autosynth_codegen::builder::{FunctionBuilder, VRegOrRef};
use autosynth_ir::{BlockId, VRegSource};

/// Per-block wasm region state — named stacks of VRegOrRef.
#[derive(Clone)]
pub struct WasmBlock {
    pub regions: BTreeMap<&'static str, Vec<VRegOrRef>>,
}

impl WasmBlock {
    /// Create the successor block from the first predecessor.
    pub fn fork(&self, source: BlockId, builder: &mut FunctionBuilder) -> WasmBlock {
        let regions = self.regions.iter().map(|(&name, slots)| {
            let wrapped: Vec<VRegOrRef> = slots.iter().map(|&val| {
                match val {
                    VRegOrRef::Ref(_) => val,
                    VRegOrRef::VReg(vreg) => {
                        let ref_id = builder.alloc_ref(source, vreg);
                        VRegOrRef::Ref(ref_id)
                    }
                }
            }).collect();
            (name, wrapped)
        }).collect();
        WasmBlock { regions }
    }

    /// Merge another predecessor's state into this block.
    pub fn merge(
        &mut self,
        other: &WasmBlock,
        new_pred: BlockId,
        builder: &mut FunctionBuilder,
    ) {
        for (name, slots) in self.regions.iter_mut() {
            let other_slots = &other.regions[name];
            for i in 0..slots.len() {
                let ref_id = match slots[i] {
                    VRegOrRef::Ref(id) => id,
                    _ => unreachable!("successor slots should all be refs from fork"),
                };
                let new_vreg = builder.resolve(other_slots[i]);
                let existing = builder.ref_source(ref_id);

                if existing.vreg == new_vreg {
                    continue;
                }

                let new_source = VRegSource { block: new_pred, vreg: new_vreg };
                if let Some(phi) = builder.merge_phi(existing, new_source) {
                    // Ref now points to the phi VReg. The block on
                    // the ref doesn't matter — the phi's sources
                    // carry the real block info.
                    builder.set_ref(ref_id, existing.block, phi);
                }
            }
        }
    }

    pub fn region(&mut self, name: &str) -> &mut Vec<VRegOrRef> {
        self.regions.get_mut(name).expect(name)
    }

    pub fn region_ref(&self, name: &str) -> &[VRegOrRef] {
        &self.regions[name]
    }
}
