use std::collections::BTreeMap;
use autosynth_codegen::builder::{FunctionBuilder, VRegOrRef};

/// Per-block wasm region state — named stacks of VRegOrRef.
#[derive(Clone)]
pub struct WasmBlock {
    pub regions: BTreeMap<&'static str, Vec<VRegOrRef>>,
}

impl WasmBlock {
    /// Create the successor block from the first predecessor.
    /// Bare VRegs get wrapped in refs so that future predecessors
    /// can mutate them to Phi. Values already wrapped are kept as-is.
    pub fn fork(&self, builder: &mut FunctionBuilder) -> WasmBlock {
        let regions = self.regions.iter().map(|(&name, slots)| {
            let wrapped: Vec<VRegOrRef> = slots.iter().map(|&val| {
                match val {
                    VRegOrRef::Ref(_) => val,
                    VRegOrRef::VReg(vreg) => {
                        let ref_id = builder.alloc_ref(vreg);
                        VRegOrRef::Ref(ref_id)
                    }
                }
            }).collect();
            (name, wrapped)
        }).collect();
        WasmBlock { regions }
    }

    /// Merge another predecessor's state into this block.
    /// Each slot is a Ref (from fork). If the new value differs:
    /// - If the ref's VReg is not yet a Phi, create a new Phi VReg
    ///   with both values, update the ref.
    /// - If already a Phi, push the new source onto it.
    pub fn merge(&mut self, other: &WasmBlock, builder: &mut FunctionBuilder) {
        for (name, slots) in self.regions.iter_mut() {
            let other_slots = &other.regions[name];
            for i in 0..slots.len() {
                let ref_id = match slots[i] {
                    VRegOrRef::Ref(id) => id,
                    _ => unreachable!("successor slots should all be refs from fork"),
                };
                let new_vreg = builder.resolve(other_slots[i]);
                let existing_vreg = builder.ref_vreg(ref_id);

                if existing_vreg == new_vreg {
                    continue;
                }

                if let Some(phi) = builder.merge_phi(existing_vreg, new_vreg) {
                    builder.set_ref(ref_id, phi);
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
