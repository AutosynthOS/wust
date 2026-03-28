use std::collections::BTreeMap;
use autosynth_codegen::builder::{FunctionBuilder, VRefSource, VRegOrRef};

/// Per-block wasm region state — named stacks of VRegOrRef.
#[derive(Clone)]
pub struct WasmBlock {
    pub regions: BTreeMap<&'static str, Vec<VRegOrRef>>,
}

impl WasmBlock {
    pub fn fork(&self) -> WasmBlock {
        self.clone()
    }

    /// Merge another predecessor's state into this block.
    pub fn merge(&mut self, other: &WasmBlock, builder: &mut FunctionBuilder) {
        for (name, slots) in self.regions.iter_mut() {
            let other_slots = &other.regions[name];
            for i in 0..slots.len() {
                if slots[i] != other_slots[i] {
                    let mut sources = Vec::new();
                    collect_sources(slots[i], builder, &mut sources);
                    collect_sources(other_slots[i], builder, &mut sources);
                    let ref_id = builder.alloc_ref(VRefSource::Phi(sources));
                    slots[i] = VRegOrRef::Ref(ref_id);
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

fn collect_sources(val: VRegOrRef, builder: &FunctionBuilder, out: &mut Vec<VRegOrRef>) {
    match val {
        VRegOrRef::VReg(_) => out.push(val),
        VRegOrRef::Ref(ref_id) => {
            match builder.ref_source(ref_id) {
                VRefSource::Direct(inner) => collect_sources(*inner, builder, out),
                VRefSource::Phi(sources) => out.extend_from_slice(sources),
            }
        }
    }
}
