use super::block_builder::BlockBuilder;
use super::code_builder::CodeBuilder;
use crate::ir::block::{BlockId, IrBlock};
use crate::ir::function::{IRFunction, VStackDef};
use crate::ir::instruction::IrInst;
use crate::ir::{CanonSlot, IrType, Register, VReg, VRegDef, VStackId, Value};

/// Configuration for creating a virtual stack.
///
/// A virtual stack is anchored to a base register plus a byte offset.
/// All slot addresses within the stack are computed relative to this anchor.
pub struct VStack {
    /// Display label for this vstack (used as a debug column header).
    pub label: &'static str,
    /// The register that serves as the base address for this stack.
    pub base: Register,
    /// Byte offset from the base register to the start of the stack.
    pub offset: u32,
}

/// Incrementally builds an [`IRFunction`] by managing virtual stacks, blocks,
/// and VReg allocation.
///
/// Holds a mutable reference to the [`CodeBuilder`], so debug recording
/// happens automatically on every [`emit`](Self::emit) call. Debug forwarding
/// methods like [`begin_op`](Self::begin_op) and [`mark_block_start`](Self::mark_block_start)
/// are no-ops when no debugger is attached to the CodeBuilder.
///
/// # Usage pattern
///
/// ```text
/// let mut f = FunctionBuilder::new(&mut code_builder);
/// let operands = f.define_vstack(VStack { label: "operands", base, offset: 0 });
/// f.entry_block(BlockId::Entry);
/// f.push_i32(operands, Value::ConstI32(42));
/// let val = f.pop_i32(operands);
/// f.emit(IrInst::Return { values: vec![val], flush: false });
/// f.build();
/// ```
pub struct FunctionBuilder<'a> {
    /// The code builder that collects finalized functions and holds the debugger.
    cb: &'a mut CodeBuilder,

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

impl<'a> FunctionBuilder<'a> {
    /// Create an empty function builder linked to a [`CodeBuilder`].
    pub fn new(cb: &'a mut CodeBuilder) -> Self {
        Self {
            cb,
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
        self.cb.add_column(vstack.label);
        self.vstacks.push(VStackDef {
            id,
            base: vstack.base,
            base_offset: vstack.offset,
            depth: 0,
            slots: Vec::new(),
        });
        id
    }

    /// Pre-define a slot in a vstack at a specific index.
    ///
    /// Used for declaring function parameters and zero-initialized locals
    /// before entering any block, or for writing to an existing slot
    /// (e.g. `local.set`) when inside an active block.
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

    /// Allocate a new i32 destination VReg on the vstack for an instruction result.
    ///
    /// The returned VReg is a placeholder — the actual value is defined
    /// when the caller emits an ALU or Cmp instruction targeting it.
    pub fn push_i32_vreg(&mut self, vstack: VStackId) -> VReg {
        // Value::Const(0) is a placeholder — the emit will define the actual value
        self.push_typed(vstack, IrType::I32, Value::ConstI64(0))
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
    ///
    /// # Panics
    ///
    /// Panics if the slot at `index` was never defined via [`define_slot`](Self::define_slot)
    /// or [`push_typed`](Self::push_typed).
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
    ///
    /// Automatically records a block boundary in the debugger (if attached).
    pub fn switch_to_block(&mut self, block: BlockId) {
        self.cb.mark_block_start(block);
        let idx = self.ensure_block(block);
        self.current_block = Some(idx);
    }

    /// Set the entry block.
    pub fn entry_block(&mut self, block: BlockId) {
        self.switch_to_block(block);
    }

    /// Create a generated block with an auto-incremented ID.
    ///
    /// Returns a [`BlockId::Gen`] that can be used as a branch target.
    /// Useful for codegen-internal blocks (cold paths, stubs, trampolines)
    /// that have no corresponding source-level position.
    pub fn gen_block(&mut self) -> BlockId {
        let id = BlockId::Gen(self.next_gen_id);
        self.next_gen_id += 1;
        self.ensure_block(id);
        id
    }

    /// Get the currently active block's ID.
    ///
    /// # Panics
    ///
    /// Panics if no block has been activated via [`switch_to_block`](Self::switch_to_block).
    pub fn current_block(&self) -> BlockId {
        let idx = self.current_block.expect("no active block");
        self.blocks[idx].id
    }

    /// Emit an IR instruction into the currently active block.
    ///
    /// Automatically records the emission into the debugger (if attached).
    ///
    /// # Panics
    ///
    /// Panics if no block is active.
    pub fn emit(&mut self, inst: IrInst) {
        let idx = self.current_block.expect("emit: no active block");
        self.blocks[idx].push(inst);
        self.cb.record_ir_emit();
    }

    /// Get the VRegDef for a given VReg.
    pub fn vreg_def(&self, vreg: VReg) -> VRegDef {
        self.vreg_defs[vreg.0 as usize]
    }

    // --- Debug forwarding (no-op when no debugger attached) ---

    /// Open a new source operation group in the debugger.
    ///
    /// Automatically snapshots every vstack's current state into its
    /// corresponding debug column.
    pub fn begin_op(&mut self, pc: &str, label: &str) {
        self.cb.begin_op(pc, label);
        for (i, vs) in self.vstacks.iter().enumerate() {
            let snapshot = format_vstack_snapshot(vs);
            self.cb.set_column(i, &snapshot);
        }
    }

    /// Finalize — analyze control flow and produce the IRFunction.
    ///
    /// Two-pass liveness analysis:
    /// 1. Params = VRegs used in a block but not defined there (live-in).
    /// 2. Results = VRegs defined in a block that appear in any successor's
    ///    params (live-out). A def that no successor needs is dead and not
    ///    included in results.
    pub fn build(self) {
        // Pass 1: compute params and successors for each block.
        let block_ids: Vec<BlockId> = self.blocks.iter().map(|bb| bb.id).collect();
        let proto_blocks: Vec<_> = self
            .blocks
            .into_iter()
            .enumerate()
            .map(|(i, bb)| {
                let mut successors = extract_successors(&bb.instructions);

                // Implicit fallthrough: if no terminator, the next block is the successor.
                if successors.is_empty() && !is_terminator(bb.instructions.last()) {
                    if let Some(&next_id) = block_ids.get(i + 1) {
                        successors.push(next_id);
                    }
                }

                let mut params = Vec::new();
                for &u in &bb.uses {
                    if !bb.defs.contains(&u) && !params.contains(&u) {
                        params.push(u);
                    }
                }

                (bb.id, bb.defs, bb.instructions, params, successors)
            })
            .collect();

        // Pass 2: compute results — a def is live-out only if a successor
        // block has it in its params (i.e., actually needs it).
        let all_params: Vec<Vec<VReg>> = proto_blocks
            .iter()
            .map(|(_, _, _, p, _)| p.clone())
            .collect();
        let all_ids: Vec<BlockId> = proto_blocks.iter().map(|(id, _, _, _, _)| *id).collect();

        let blocks = proto_blocks
            .into_iter()
            .map(|(id, defs, instructions, params, successors)| {
                // Results = values this block passes to successors OR returns.
                let mut results = Vec::new();

                // 1. Values (defs or pass-through params) needed by successors.
                let available: Vec<VReg> = defs.iter().chain(params.iter()).copied().collect();
                for &v in &available {
                    if results.contains(&v) {
                        continue;
                    }
                    let needed = successors.iter().any(|succ_id| {
                        if let Some(idx) = all_ids.iter().position(|id| id == succ_id) {
                            all_params[idx].contains(&v)
                        } else {
                            false
                        }
                    });
                    if needed {
                        results.push(v);
                    }
                }

                // 2. Return values — the block's output to the caller.
                if let Some(IrInst::Return { values, .. }) = instructions.last() {
                    for &v in values {
                        if !results.contains(&v) {
                            results.push(v);
                        }
                    }
                }

                IrBlock {
                    id,
                    params,
                    results,
                    successors,
                    instructions,
                }
            })
            .collect();

        let func = IRFunction {
            vstacks: self.vstacks,
            vreg_defs: self.vreg_defs,
            blocks,
        };

        self.cb.push_function(func);
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
            slot: Some(slot),
            value,
        });
        id
    }

    /// Allocate a temp VReg with no canonical stack slot.
    ///
    /// Temps cannot be spilled — they must be consumed immediately
    /// (e.g. a comparison result feeding the next `BrIf`) or be
    /// rematerializable from a constant value.
    pub fn alloc_temp(&mut self, ty: IrType, value: Value) -> VReg {
        let id = VReg(self.next_vreg);
        self.next_vreg += 1;
        self.vreg_defs.push(VRegDef {
            id,
            ty,
            slot: None,
            value,
        });
        self.record_def(id);
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
        let vreg = vs.slots[vs.depth as usize].expect("pop: slot not defined");
        self.record_use(vreg);
        let def = self.vreg_defs[vreg.0 as usize];
        self.emit(IrInst::StackPop { def });
        vreg
    }
}

/// Extract successor block IDs from the last instruction in a block.
fn extract_successors(instructions: &[IrInst]) -> Vec<BlockId> {
    match instructions.last() {
        Some(IrInst::BrIf {
            block_if,
            block_else,
            ..
        }) => {
            vec![*block_if, *block_else]
        }
        Some(IrInst::Branch { target }) => {
            vec![*target]
        }
        Some(IrInst::Return { .. }) => Vec::new(),
        _ => Vec::new(), // fallthrough or no terminator yet
    }
}

/// Check if an instruction is a block terminator (no fallthrough).
fn is_terminator(inst: Option<&IrInst>) -> bool {
    matches!(
        inst,
        Some(IrInst::BrIf { .. } | IrInst::Branch { .. } | IrInst::Return { .. })
    )
}

fn ir_type_size(ty: IrType) -> u8 {
    match ty {
        IrType::I32 | IrType::F32 => 4,
        IrType::I64 | IrType::F64 => 8,
        IrType::V128 => 16,
    }
}

/// Format a vstack's current slots as a space-separated list of VReg names.
fn format_vstack_snapshot(vs: &VStackDef) -> String {
    let mut parts = Vec::new();
    for slot in vs.slots.iter().take(vs.depth as usize) {
        match slot {
            Some(vreg) => parts.push(format!("{vreg}")),
            None => parts.push("_".into()),
        }
    }
    parts.join(" ")
}
