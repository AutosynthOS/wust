use super::block_builder::BlockBuilder;
use super::code_builder::CodeBuilder;
use crate::ir::block::{BlockId, IrBlock};
use crate::ir::function::{IRFunction, VStackDef};
use crate::ir::instruction::IrInst;
use crate::ir::{CanonSlot, IrType, Register, VReg, VRegDef, VStackId, Value};

/// Configuration for creating a virtual stack.
pub struct VStack {
    pub base: Register,
    pub offset: u32,
}

pub struct FunctionBuilder {
    /// VReg definitions, indexed by VReg id.
    vreg_defs: Vec<VRegDef>,
    next_vreg: u32,

    /// Virtual stack state (shared across all blocks).
    vstacks: Vec<VStackDef>,

    /// All block builders, indexed by position.
    blocks: Vec<BlockBuilder>,
    /// Index of the currently active block builder.
    current_block: Option<usize>,
    /// Next generated block ID (for suspend stubs, cold paths, etc.).
    next_gen_id: u32,
}

impl FunctionBuilder {
    pub fn new() -> Self {
        Self {
            vreg_defs: Vec::new(),
            next_vreg: 0,
            vstacks: Vec::new(),
            blocks: Vec::new(),
            current_block: None,
            next_gen_id: 0,
        }
    }

    /// Register a new virtual stack anchored to a register + offset.
    pub fn define_vstack(&mut self, vstack: VStack) -> VStackId {
        let id = VStackId(self.vstacks.len() as u32);
        self.vstacks.push(VStackDef {
            id,
            base: vstack.base,
            base_offset: vstack.offset,
            depth: 0,
            slots: Vec::new(),
        });
        id
    }

    /// Pre-define a slot in a vstack (e.g. for function params, zero-init locals).
    pub fn define_slot(&mut self, vstack: VStackId, index: usize, ty: IrType, value: Value) {
        let size = ir_type_size(ty);
        let base_offset = self.vstacks[vstack.0 as usize].base_offset;

        // Grow the slot table if needed
        let vs = &mut self.vstacks[vstack.0 as usize];
        while vs.slots.len() <= index {
            vs.slots.push(None);
        }

        let byte_offset = base_offset + (index as u32) * (size as u32);
        let slot = CanonSlot {
            vstack,
            index: index as u32,
            byte_offset,
            size,
        };

        // If value references another VReg, record a use of the source.
        if let Value::VReg(src) = value {
            self.record_use(src);
        }

        let vreg = self.alloc_vreg(ty, slot, value);
        self.record_def(vreg);

        // Emit a StackPush when inside an active block (local.set).
        // No-op for initial declarations (no active block yet).
        if self.current_block.is_some() {
            let def = self.vreg_defs[vreg.0 as usize];
            self.emit(IrInst::StackPush { def });
        }

        self.vstacks[vstack.0 as usize].slots[index] = Some(vreg);

        let vs = &mut self.vstacks[vstack.0 as usize];
        if vs.depth <= index as u32 {
            vs.depth = index as u32 + 1;
        }
    }

    /// Push a constant i32 onto a vstack.
    pub fn push_i32(&mut self, vstack: VStackId, value: Value) -> VReg {
        self.push_typed(vstack, IrType::I32, value)
    }

    /// Push a constant i64 onto a vstack.
    pub fn push_i64(&mut self, vstack: VStackId, value: Value) -> VReg {
        self.push_typed(vstack, IrType::I64, value)
    }

    /// Push an existing VReg onto a vstack (e.g. local.get pushes a local's vreg).
    pub fn push_vreg(&mut self, vstack: VStackId, src: VReg) -> VReg {
        let src_def = self.vreg_defs[src.0 as usize];
        self.push_typed(vstack, src_def.ty, Value::VReg(src))
    }

    /// Allocate a new destination VReg on the vstack — for instruction results.
    pub fn push_i32_vreg(&mut self, vstack: VStackId) -> VReg {
        // Value::Const(0) is a placeholder — the emit will define the actual value
        self.push_typed(vstack, IrType::I32, Value::Const(0))
    }

    /// Pop the top i32 from a vstack, returning the VReg that was there.
    pub fn pop_i32(&mut self, vstack: VStackId) -> VReg {
        self.pop(vstack)
    }

    /// Pop the top i64 from a vstack, returning the VReg that was there.
    pub fn pop_i64(&mut self, vstack: VStackId) -> VReg {
        self.pop(vstack)
    }

    /// Read a slot from a vstack by index (non-consuming, e.g. local.get).
    pub fn get_slot(&mut self, vstack: VStackId, index: usize) -> VReg {
        let vs = &self.vstacks[vstack.0 as usize];
        let vreg = vs.slots[index].expect("get_slot: slot not defined");
        self.record_use(vreg);
        vreg
    }

    /// Get the current operand stack depth of a vstack.
    pub fn stack_depth(&self, vstack: VStackId) -> u32 {
        self.vstacks[vstack.0 as usize].depth
    }

    /// Switch to a block — creates the block builder if it doesn't exist.
    pub fn switch_to_block(&mut self, block: BlockId) {
        let idx = self.ensure_block(block);
        self.current_block = Some(idx);
    }

    /// Set the entry block.
    pub fn entry_block(&mut self, block: BlockId) {
        self.switch_to_block(block);
    }

    /// Create a generated block (for suspend stubs, cold paths, etc.).
    pub fn gen_block(&mut self) -> BlockId {
        let id = BlockId::Gen(self.next_gen_id);
        self.next_gen_id += 1;
        self.ensure_block(id);
        id
    }

    /// Get the currently active block.
    pub fn current_block(&self) -> BlockId {
        let idx = self.current_block.expect("no active block");
        self.blocks[idx].id
    }

    /// Attach a debug label to the current position.
    pub fn label(&mut self, _name: &str) {
        // TODO: store labels for debug/disassembly
    }

    /// Emit an IR instruction into the current block.
    pub fn emit(&mut self, inst: IrInst) {
        let idx = self.current_block.expect("emit: no active block");
        self.blocks[idx].push(inst);
    }

    /// Finalize — analyze control flow and produce the IRFunction.
    ///
    /// Computes block params (VRegs used but not defined in the block —
    /// they must come from predecessors) and results (VRegs defined in
    /// the block that successors might need).
    pub fn build(self, cb: &mut CodeBuilder) {
        let blocks = self.blocks.into_iter().map(|bb| {
            let successors = extract_successors(&bb.instructions);

            // Params = VRegs used in this block that weren't defined here (deduplicated).
            let mut params = Vec::new();
            for &u in &bb.uses {
                if !bb.defs.contains(&u) && !params.contains(&u) {
                    params.push(u);
                }
            }

            // Results = VRegs defined in this block (deduplicated).
            let mut results = Vec::new();
            for &d in &bb.defs {
                if !results.contains(&d) {
                    results.push(d);
                }
            }

            IrBlock {
                id: bb.id,
                params,
                results,
                successors,
                instructions: bb.instructions,
            }
        }).collect();

        let func = IRFunction {
            vstacks: self.vstacks,
            vreg_defs: self.vreg_defs,
            blocks,
        };

        cb.push_function(func);
    }

    // --- internal helpers ---

    fn record_def(&mut self, vreg: VReg) {
        if let Some(idx) = self.current_block {
            self.blocks[idx].record_def(vreg);
        }
    }

    fn record_use(&mut self, vreg: VReg) {
        if let Some(idx) = self.current_block {
            self.blocks[idx].record_use(vreg);
        }
    }

    fn alloc_vreg(&mut self, ty: IrType, slot: CanonSlot, value: Value) -> VReg {
        let id = VReg(self.next_vreg);
        self.next_vreg += 1;
        self.vreg_defs.push(VRegDef {
            id,
            ty,
            slot,
            value,
        });
        id
    }

    fn ensure_block(&mut self, id: BlockId) -> usize {
        if let Some(idx) = self.blocks.iter().position(|b| b.id == id) {
            idx
        } else {
            self.blocks.push(BlockBuilder::new(id));
            self.blocks.len() - 1
        }
    }

    fn push_typed(&mut self, vstack: VStackId, ty: IrType, value: Value) -> VReg {
        let vs = &self.vstacks[vstack.0 as usize];
        let index = vs.depth;
        let size = ir_type_size(ty);
        let byte_offset = vs.base_offset + index * (size as u32);

        let slot = CanonSlot {
            vstack,
            index,
            byte_offset,
            size,
        };

        // If the value references another VReg, record a use of the source.
        if let Value::VReg(src) = value {
            self.record_use(src);
        }

        let vreg = self.alloc_vreg(ty, slot, value);
        self.record_def(vreg);

        let def = self.vreg_defs[vreg.0 as usize];
        self.emit(IrInst::StackPush { def });

        let vs = &mut self.vstacks[vstack.0 as usize];
        let idx = index as usize;
        if idx < vs.slots.len() {
            vs.slots[idx] = Some(vreg);
        } else {
            vs.slots.push(Some(vreg));
        }
        vs.depth += 1;

        vreg
    }

    fn pop(&mut self, vstack: VStackId) -> VReg {
        let vs = &mut self.vstacks[vstack.0 as usize];
        assert!(vs.depth > 0, "pop: vstack is empty");
        vs.depth -= 1;
        let vreg = vs.slots[vs.depth as usize]
            .expect("pop: slot not defined");
        self.record_use(vreg);
        let def = self.vreg_defs[vreg.0 as usize];
        self.emit(IrInst::StackPop { def });
        vreg
    }
}

/// Extract successor block IDs from the last instruction in a block.
fn extract_successors(instructions: &[IrInst]) -> Vec<BlockId> {
    match instructions.last() {
        Some(IrInst::BrIf { block_if, block_else, .. }) => {
            vec![*block_if, *block_else]
        }
        Some(IrInst::Branch { target }) => {
            vec![*target]
        }
        Some(IrInst::Return { .. }) => Vec::new(),
        _ => Vec::new(), // fallthrough or no terminator yet
    }
}

fn ir_type_size(ty: IrType) -> u8 {
    match ty {
        IrType::I32 | IrType::F32 => 4,
        IrType::I64 | IrType::F64 => 8,
        IrType::V128 => 16,
    }
}
