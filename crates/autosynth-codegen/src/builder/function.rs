use std::collections::BTreeMap;
use std::cell::RefCell;
use std::rc::Rc;
use autosynth_ir::{BlockId, Operand, VCode, VReg, VRegSource};
use autosynth_isa::{PReg, Width};
use autosynth_regalloc::{MachineConfig, SharedVRegAllocator, VRegAllocator, VRegState};

use super::{BlockBuilder, BuilderItem, VRefId, VRegOrRef};
use super::block::SharedBlockBuilder;
use crate::ir::{IrBlock, IrFunction, block_order};

/// Builds a function's VCode representation.
pub struct FunctionBuilder {
    pub alloc: SharedVRegAllocator,
    config: MachineConfig,
    blocks: BTreeMap<BlockId, SharedBlockBuilder>,
    current_block: BlockId,
    refs: Vec<VRegSource>,
}

impl FunctionBuilder {
    pub fn new(config: MachineConfig) -> Self {
        let alloc: SharedVRegAllocator = Rc::new(RefCell::new(VRegAllocator::new()));
        let entry = BlockId::Entry(1);
        let mut blocks = BTreeMap::new();
        blocks.insert(entry, Rc::new(RefCell::new(BlockBuilder::new(entry))));
        Self {
            alloc,
            config,
            blocks,
            current_block: entry,
            refs: Vec::new(),
        }
    }

    /// Get the shared block builder for a block.
    pub fn block(&self, id: BlockId) -> SharedBlockBuilder {
        self.blocks[&id].clone()
    }

    pub fn define(&mut self, state: VRegState) -> VReg {
        let vreg = self.alloc.borrow_mut().define(state);
        self.blocks[&self.current_block].borrow_mut().defs.push(vreg);
        vreg
    }

    pub fn width(&self, vreg: VReg) -> Width {
        self.alloc.borrow().width(vreg)
    }

    pub fn emit(&mut self, inst: VCode) {
        self.blocks[&self.current_block].borrow_mut().emit(inst);
    }

    pub fn push_operand(&mut self, val: impl Into<VRegOrRef>) {
        self.blocks[&self.current_block].borrow_mut().push_operand(val);
    }

    pub fn current_block_id(&self) -> BlockId {
        self.current_block
    }

    pub fn start_block(&mut self, id: BlockId) {
        self.blocks.entry(id).or_insert_with(|| Rc::new(RefCell::new(BlockBuilder::new(id))));
        self.current_block = id;
    }

    // --- Ref table ---

    pub fn alloc_ref(&mut self, block: BlockId, vreg: VReg) -> VRefId {
        let id = VRefId(self.refs.len() as u32);
        self.refs.push(VRegSource { block, vreg });
        id
    }

    pub fn ref_source(&self, id: VRefId) -> VRegSource {
        self.refs[id.0 as usize]
    }

    pub fn ref_vreg(&self, id: VRefId) -> VReg {
        self.refs[id.0 as usize].vreg
    }

    pub fn set_ref(&mut self, id: VRefId, block: BlockId, vreg: VReg) {
        self.refs[id.0 as usize] = VRegSource { block, vreg };
    }

    /// Merge a new source into a phi. If the existing VReg is already
    /// a Phi, pushes the new source. Otherwise creates a new Phi VReg,
    /// inheriting the target constraint, and returns it.
    pub fn merge_phi(
        &mut self,
        existing: VRegSource,
        new_source: VRegSource,
    ) -> Option<VReg> {
        let mut alloc = self.alloc.borrow_mut();
        let st = alloc.state_mut(existing.vreg);
        match &mut st.phi {
            Some(sources) => {
                sources.push(new_source);
                None
            }
            None => {
                let width = st.width;
                let target = st.target;
                let phi = alloc.define(VRegState {
                    phi: Some(vec![existing, new_source]),
                    ..VRegState::new(width)
                });
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
            VRegOrRef::Ref(ref_id) => self.refs[ref_id.0 as usize].vreg,
        }
    }

    // --- Build ---

    pub fn build(self) -> IrFunction {
        let successors: BTreeMap<BlockId, Vec<BlockId>> = self.blocks.iter()
            .map(|(&id, b)| (id, b.borrow().successors()))
            .collect();

        let mut predecessors: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
        for (&id, succs) in &successors {
            for &succ in succs {
                predecessors.entry(succ).or_default().push(id);
            }
        }

        let order = block_order::rpo(BlockId::Entry(1), &successors);

        let blocks = self.blocks.into_iter().map(|(id, shared_b)| {
            let b = Rc::try_unwrap(shared_b)
                .unwrap_or_else(|_| panic!("block {id:?} still borrowed"))
                .into_inner();

            let mut stream = std::collections::VecDeque::new();
            let mut params = Vec::new();

            for item in b.stream {
                match item {
                    BuilderItem::Operand(val) => {
                        let vreg = match val {
                            VRegOrRef::VReg(vreg) => vreg,
                            VRegOrRef::Ref(ref_id) => {
                                let vreg = self.refs[ref_id.0 as usize].vreg;
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
            config: self.config,
            blocks,
            block_order: order,
        }
    }
}
