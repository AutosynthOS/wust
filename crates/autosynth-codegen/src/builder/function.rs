use std::collections::BTreeMap;
use std::cell::RefCell;
use std::rc::Rc;
use autosynth_ir::{BlockId, Operand, VCode, VReg};
use autosynth_isa::{PReg, Width};
use autosynth_regalloc::{SharedVRegAllocator, VInit, VRegAllocator};

use super::{BlockBuilder, BuilderItem, VRefId, VRegOrRef};
use crate::ir::{IrBlock, IrFunction, block_order};

/// Builds a function's VCode representation.
pub struct FunctionBuilder {
    alloc: SharedVRegAllocator,
    blocks: BTreeMap<BlockId, BlockBuilder>,
    current_block: BlockId,
    /// Ref table — each ref maps to a VReg.
    refs: Vec<VReg>,
}

impl FunctionBuilder {
    pub fn new() -> Self {
        let alloc: SharedVRegAllocator = Rc::new(RefCell::new(VRegAllocator::new()));
        let entry = BlockId::Entry;
        let mut blocks = BTreeMap::new();
        blocks.insert(entry, BlockBuilder::new(entry));
        Self {
            alloc,
            blocks,
            current_block: entry,
            refs: Vec::new(),
        }
    }

    /// Define a new VReg, recording it as a def on the current block.
    pub fn define(&mut self, init: VInit, width: Width) -> VReg {
        let vreg = self.alloc.borrow_mut().define(init, width);
        self.current_block_mut().defs.push(vreg);
        vreg
    }

    pub fn emit(&mut self, inst: VCode) {
        self.current_block_mut().emit(inst);
    }

    pub fn push_operand(&mut self, val: impl Into<VRegOrRef>) {
        self.current_block_mut().push_operand(val);
    }

    pub fn current_block_id(&self) -> BlockId {
        self.current_block
    }

    pub fn current_block(&self) -> &BlockBuilder {
        self.blocks.get(&self.current_block).unwrap()
    }

    pub fn current_block_mut(&mut self) -> &mut BlockBuilder {
        self.blocks.get_mut(&self.current_block).unwrap()
    }

    pub fn start_block(&mut self, id: BlockId) {
        self.blocks.entry(id).or_insert_with(|| BlockBuilder::new(id));
        self.current_block = id;
    }

    // --- Ref table ---

    pub fn alloc_ref(&mut self, vreg: VReg) -> VRefId {
        let id = VRefId(self.refs.len() as u32);
        self.refs.push(vreg);
        id
    }

    pub fn ref_vreg(&self, id: VRefId) -> VReg {
        self.refs[id.0 as usize]
    }

    pub fn set_ref(&mut self, id: VRefId, vreg: VReg) {
        self.refs[id.0 as usize] = vreg;
    }

    /// Merge a new source into a phi. If the existing VReg is already
    /// a Phi, pushes the new source. Otherwise creates a new Phi VReg,
    /// inheriting the target constraint, and returns it.
    /// Returns `Some(new_phi)` if a new VReg was created, `None` if
    /// the source was pushed onto an existing phi.
    pub fn merge_phi(&mut self, existing: VReg, new_source: VReg) -> Option<VReg> {
        let mut alloc = self.alloc.borrow_mut();
        let def = alloc.def_mut(existing);
        match &mut def.init {
            VInit::Phi(sources) => {
                sources.push(new_source);
                None
            }
            _ => {
                let width = def.width;
                let target = def.target;
                let phi = alloc.define(
                    VInit::Phi(vec![existing, new_source]),
                    width,
                );
                if let Some(preg) = target {
                    alloc.set_target(phi, preg);
                }
                Some(phi)
            }
        }
    }

    pub fn set_target(&mut self, val: VRegOrRef, preg: PReg) {
        let vreg = self.resolve(val);
        self.alloc.borrow_mut().set_target(vreg, preg);
    }

    pub fn resolve(&self, val: VRegOrRef) -> VReg {
        match val {
            VRegOrRef::VReg(vreg) => vreg,
            VRegOrRef::Ref(ref_id) => self.refs[ref_id.0 as usize],
        }
    }

    // --- Build ---

    pub fn build(self) -> IrFunction {
        let successors: BTreeMap<BlockId, Vec<BlockId>> = self.blocks.iter()
            .map(|(&id, b)| (id, b.successors()))
            .collect();

        let mut predecessors: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
        for (&id, succs) in &successors {
            for &succ in succs {
                predecessors.entry(succ).or_default().push(id);
            }
        }

        let order = block_order::rpo(BlockId::Entry, &successors);

        let blocks = self.blocks.into_iter().map(|(id, b)| {
            let mut stream = std::collections::VecDeque::new();
            let mut params = Vec::new();

            for item in b.stream {
                match item {
                    BuilderItem::Operand(val) => {
                        let vreg = match val {
                            VRegOrRef::VReg(vreg) => vreg,
                            VRegOrRef::Ref(ref_id) => {
                                let vreg = self.refs[ref_id.0 as usize];
                                if !params.contains(&vreg) {
                                    params.push(vreg);
                                }
                                vreg
                            }
                        };
                        stream.push_back(VCode::Operand(Operand::VReg(vreg)));
                    }
                    BuilderItem::Inst(inst) => {
                        stream.push_back(inst);
                    }
                }
            }

            (id, IrBlock {
                id,
                stream,
                successors: successors.get(&id).cloned().unwrap_or_default(),
                predecessors: predecessors.remove(&id).unwrap_or_default(),
                defs: b.defs,
                params,
                results: Vec::new(),
            })
        }).collect();

        IrFunction {
            alloc: self.alloc,
            blocks,
            block_order: order,
        }
    }
}
