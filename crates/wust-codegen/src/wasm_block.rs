use autosynth_codegen::builder::{BlockBuilder, FunctionBuilder, SharedBlockBuilder, VRegOrRef};
use autosynth_ir::{BlockId, VRegSource};
use autosynth_regalloc::{SharedVRegAllocator, VRegAllocator};
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::rc::{Rc, Weak};

use crate::region::StackRegion;

/// Per-block wasm state — named stack regions + weak refs to builder internals.
#[derive(Clone)]
pub struct WasmBlock {
    pub regions: BTreeMap<&'static str, StackRegion>,
    pub block: Weak<RefCell<BlockBuilder>>,
    pub alloc: Weak<RefCell<VRegAllocator>>,
}

impl WasmBlock {
    pub fn new(
        regions: BTreeMap<&'static str, StackRegion>,
        block: &SharedBlockBuilder,
        alloc: &SharedVRegAllocator,
    ) -> Self {
        Self {
            regions,
            block: Rc::downgrade(block),
            alloc: Rc::downgrade(alloc),
        }
    }
}

impl WasmBlock {
    pub fn fork(&self, source: BlockId, builder: &mut FunctionBuilder) -> WasmBlock {
        let regions = self
            .regions
            .iter()
            .map(|(&name, region)| {
                let mut forked = region.clone();
                for vreg_or_ref in forked.entries_mut() {
                    match vreg_or_ref {
                        VRegOrRef::Ref(_) => {}
                        VRegOrRef::VReg(vreg) => {
                            let ref_id = builder.alloc_ref(source, *vreg);
                            *vreg_or_ref = VRegOrRef::Ref(ref_id);
                        }
                    }
                }
                (name, forked)
            })
            .collect();
        WasmBlock {
            regions,
            block: Weak::new(), // set when block is created in ensure_or_merge
            alloc: self.alloc.clone(),
        }
    }

    pub fn merge(&mut self, other: &WasmBlock, new_pred: BlockId, builder: &mut FunctionBuilder) {
        for (name, region) in self.regions.iter_mut() {
            let other_region = &other.regions[name];
            for i in 0..region.len() {
                let ref_id = match region.get(i) {
                    VRegOrRef::Ref(id) => *id,
                    _ => unreachable!("successor slots should all be refs from fork"),
                };
                let new_vreg = builder.resolve(*other_region.get(i));
                let existing = builder.ref_source(ref_id);

                if existing.vreg == new_vreg {
                    continue;
                }
                let new_source = VRegSource {
                    block: new_pred,
                    vreg: new_vreg,
                };
                if let Some(phi) = builder.merge_phi(existing, new_source) {
                    builder.set_ref(ref_id, new_pred, phi);
                }
            }
        }
    }

    pub fn region(&mut self, name: &str) -> &mut StackRegion {
        self.regions.get_mut(name).expect(name)
    }

    pub fn region_ref(&self, name: &str) -> &StackRegion {
        &self.regions[name]
    }
}
