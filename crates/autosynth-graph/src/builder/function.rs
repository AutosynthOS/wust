//! Wasm function builder — the consumer API.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::rc::Rc;

use autosynth_isa::{PReg, Width};
use wust_core::{FRAME_HEADER_SIZE, FuncIdx, FuncMeta, ValType};

use smallvec::{SmallVec, smallvec};

use crate::{
    Input, Operation, VCode, VInit, VRegKey,
    builder::{
        BlockId,
        block::WasmBlock,
        state::{BuildState, SharedBuildState},
    },
    types::{Abi, valtype_width},
};

#[derive(Debug)]
pub struct WasmFunctionBuilder {
    meta: FuncMeta,
    blocks: BTreeMap<BlockId, WasmBlock>,
    current_block: BlockId,
    state: SharedBuildState,
}

impl WasmFunctionBuilder {
    pub fn new(meta: &FuncMeta) -> Self {
        let state = Rc::new(RefCell::new(BuildState::new()));

        let operand_base = meta.locals_size + FRAME_HEADER_SIZE as u16;

        let mut func = Self {
            meta: meta.clone(),
            blocks: BTreeMap::from([(BlockId::Entry(0), WasmBlock::fresh(&state, operand_base))]),
            current_block: BlockId::Entry(0),
            state,
        };

        let entry = func.block();

        for (i, ty) in meta.params.iter().enumerate() {
            entry.define_and_push(
                "locals",
                VInit {
                    width: valtype_width(*ty),
                    constant: None,
                    preg: Some(PReg(i as u8)),
                    mem: None,
                },
            );
        }

        for ty in meta.locals.iter() {
            entry.define_and_push(
                "locals",
                VInit {
                    width: valtype_width(*ty),
                    constant: Some(0),
                    preg: None,
                    mem: None,
                },
            );
        }

        func
    }

    pub fn block(&mut self) -> &mut WasmBlock {
        self.blocks
            .get_mut(&self.current_block)
            .expect("no current block")
    }

    /// Fork the current block into a new block at `id`.
    /// The new block gets the current block's region state (cloned),
    /// but with an empty operations vec. Switches current_block to the new block.
    pub fn fork(&mut self, id: BlockId) {
        let current = self
            .blocks
            .get(&self.current_block)
            .expect("no current block");
        let mut forked = current.clone();
        forked.operations.clear();
        self.blocks.insert(id, forked);
        self.current_block = id;
    }

    pub fn switch_to(&mut self, id: BlockId) {
        self.current_block = id;
    }

    pub fn brif(&mut self, condition: Input, if_true: BlockId, if_false: BlockId) {
        let block = self.block();

        // Emit the BrIf operation in the current block
        let brif_key = block.emit(Operation {
            opcode: VCode::BrIf,
            inputs: smallvec![condition],
            defines: SmallVec::new(),
            effect: block.last_effect,
            prev: block.operations.last().copied(),
        });

        // Finalize current block and fork into both branches
        let if_true_block = block.finalize_and_fork(brif_key);
        let if_false_block = block.finalize_and_fork(brif_key);

        self.blocks.insert(if_true, if_true_block);
        self.blocks.insert(if_false, if_false_block);
    }

    pub fn emit_return(&mut self, abi: Abi) {
        let types = self.meta.results.clone();
        let block = self.block();
        let inputs = block.pop_valtypes::<SmallVec<_>>(&types);
        block.emit(Operation {
            opcode: VCode::Return { abi },
            inputs,
            effect: block.last_effect,
            prev: block.operations.last().copied(),
            defines: SmallVec::new(),
        });
    }

    pub fn into_state(mut self) -> BuildState {
        self.blocks.clear();
        std::rc::Rc::try_unwrap(self.state)
            .expect("shared state still borrowed")
            .into_inner()
    }
}
