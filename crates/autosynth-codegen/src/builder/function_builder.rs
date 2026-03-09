use autosynth_ir::Operand;
use autosynth_isa::{PReg, Width};

use super::block_builder::BlockBuilder;
use super::code_builder::CodeBuilder;
use crate::disasm::table::Align;
use crate::ir::block::{BlockId, IrBlock};
use crate::ir::function::{IRFunction, VStackConfig};
use crate::ir::instruction::IrInst;
use crate::ir::{CanonSlot, Register, VReg, VRegDef, VStackId, VStackMut, Value};

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
/// Vstack configuration (label, base register, offset) is immutable and
/// function-scoped. Vstack mutable state (depth, slot assignments) lives
/// on each [`BlockBuilder`]. Branch methods (`br`, `br_if`) clone the
/// current block's vstack state onto target blocks, and `start_block`
/// activates a block whose state was set by a prior branch.
pub struct FunctionBuilder<'a> {
    /// The code builder that collects finalized functions and holds the debugger.
    cb: &'a mut CodeBuilder,

    /// VReg definitions, indexed by VReg id.
    vreg_defs: Vec<VRegDef>,
    next_vreg: u32,

    /// Immutable vstack configurations (label, base, offset).
    vstack_configs: Vec<VStackConfig>,

    /// All block builders, indexed by position.
    blocks: Vec<BlockBuilder>,
    /// Index of the currently active block builder.
    current_block: Option<usize>,
    /// Next generated block ID (for suspend stubs, cold paths, etc.).
    next_gen_id: u32,
}

impl<'a> FunctionBuilder<'a> {
    /// Create an empty function builder linked to a [`CodeBuilder`].
    ///
    /// Automatically registers the standard source columns (pc, label).
    pub fn new(cb: &'a mut CodeBuilder) -> Self {
        cb.dbg(|dbg| {
            dbg.add_source_column("pc", Align::Right);
            dbg.add_source_column("label", Align::Left);
        });

        Self {
            cb,
            vreg_defs: Vec::new(),
            next_vreg: 0,
            vstack_configs: Vec::new(),
            blocks: Vec::new(),
            current_block: None,
            next_gen_id: 0,
        }
    }

    /// Register a new virtual stack anchored to a register + offset.
    ///
    /// Also initializes empty vstack state on the current block.
    ///
    /// # Panics
    ///
    /// Panics if no block is active (call `entry_block` first).
    pub fn define_vstack(&mut self, vstack: VStack) -> VStackId {
        let id = VStackId(self.vstack_configs.len() as u32);
        self.cb
            .dbg(|dbg| dbg.add_source_column(vstack.label, Align::Left));
        self.vstack_configs.push(VStackConfig {
            id,
            label: vstack.label,
            base: vstack.base,
            base_offset: vstack.offset,
        });
        // Initialize empty state on the current block.
        let idx = self.current_block.expect("define_vstack: no active block");
        self.blocks[idx].vstack_state.push(VStackMut {
            depth: 0,
            slots: Vec::new(),
        });
        id
    }

    /// Pre-define a slot in a vstack at a specific index.
    pub fn define_slot(&mut self, vstack: VStackId, index: usize, width: Width, value: Value) {
        let size = width.bytes() as u8;
        let base_offset = self.vstack_configs[vstack.0 as usize].base_offset;

        // Grow the slot table if needed.
        let vs = self.vstack_mut(vstack);
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

        if let Value::VReg(src) = value {
            self.record_use(src);
        }

        let vreg = self.alloc_vreg(width, slot, value);
        self.record_def(vreg);

        // Emit a Store when inside an active block (local.set).
        if self.current_block.is_some() {
            let label = self.vstack_configs[vstack.0 as usize].label;
            let base = base_preg(self.vstack_configs[slot.vstack.0 as usize].base);
            self.emit(IrInst::Store {
                src: Operand::VReg(vreg, width),
                base,
                offset: slot.byte_offset,
            });
            let op = format!("{label}[{index}] ← {vreg}");
            self.cb.dbg(|dbg| dbg.set_source("operation", &op));
        }

        self.vstack_mut(vstack).slots[index] = Some(vreg);

        let vs = self.vstack_mut(vstack);
        if vs.depth <= index as u32 {
            vs.depth = index as u32 + 1;
        }
    }

    /// Push a typed value onto a vstack, returning the VReg allocated for it.
    pub fn push(&mut self, vstack: VStackId, width: Width, value: Value) -> VReg {
        self.push_typed(vstack, width, value)
    }

    /// Allocate a destination VReg on the vstack for an instruction result.
    pub fn push_dst(&mut self, vstack: VStackId, width: Width) -> VReg {
        self.push_typed(vstack, width, Value::Destination)
    }

    /// Read a slot from a vstack by index (non-consuming, e.g. local.get).
    ///
    /// # Panics
    ///
    /// Panics if the slot at `index` was never defined.
    pub fn get_slot(&mut self, vstack: VStackId, index: usize) -> VReg {
        let vs = self.vstack_ref(vstack);
        let vreg = vs.slots[index].expect("get_slot: slot not defined");
        self.record_use(vreg);
        vreg
    }

    /// Get the current operand stack depth of a vstack.
    pub fn stack_depth(&self, vstack: VStackId) -> u32 {
        self.vstack_ref(vstack).depth
    }

    // --- Block lifecycle ---

    /// Set the entry block and register the "operation" source column.
    ///
    /// Must be called before `define_vstack` since vstacks initialize
    /// state on the current block.
    pub fn entry_block(&mut self, block: BlockId) {
        let idx = self.ensure_block(block);
        self.current_block = Some(idx);
        self.cb.dbg(|dbg| dbg.mark_block_start(block));
    }

    /// Finish vstack definitions and register the "operation" column.
    ///
    /// Call this after all `define_vstack` calls and before emitting
    /// instructions, so the operation column appears rightmost.
    pub fn finish_entry(&mut self) {
        self.cb
            .dbg(|dbg| dbg.add_source_column("operation", Align::Left));
    }

    /// Start writing a block whose vstack state was set by a prior branch.
    ///
    /// # Panics
    ///
    /// Panics if no branch has targeted this block (vstack state is empty).
    pub fn start_block(&mut self, block: BlockId) {
        let idx = self.ensure_block(block);
        assert!(
            !self.blocks[idx].vstack_state.is_empty(),
            "start_block({block}): no vstack state — was this block targeted by a branch?"
        );
        self.current_block = Some(idx);
        self.cb.dbg(|dbg| dbg.mark_block_start(block));
    }

    /// Unconditional branch — finalizes the current block.
    ///
    /// Clones the current block's vstack state onto the target block
    /// and marks the current block as finalized.
    pub fn br(&mut self, target: BlockId) {
        self.emit(IrInst::Branch { target });
        self.snapshot_vstack_onto(target);
        let idx = self.current_block.expect("br: no active block");
        self.blocks[idx].successors.push(target);
        self.blocks[idx].finalized = true;
        self.current_block = None;
    }

    /// Conditional branch — finalizes the current block.
    ///
    /// Clones the current block's vstack state onto both target blocks.
    pub fn br_if(&mut self, cond: VReg, block_if: BlockId, block_else: BlockId) {
        self.emit(IrInst::BrIf {
            cond,
            block_if,
            block_else,
        });
        self.snapshot_vstack_onto(block_if);
        self.snapshot_vstack_onto(block_else);
        let idx = self.current_block.expect("br_if: no active block");
        self.blocks[idx].successors.push(block_if);
        self.blocks[idx].successors.push(block_else);
        self.blocks[idx].finalized = true;
        self.current_block = None;
    }

    /// Return — finalizes the current block (no successors).
    pub fn ret(&mut self, values: Vec<VReg>, flush: bool) {
        self.emit(IrInst::Return { values, flush });
        let idx = self.current_block.expect("ret: no active block");
        self.blocks[idx].finalized = true;
        self.current_block = None;
    }

    /// Whether the current block has been finalized by a br/br_if/ret.
    pub fn is_finalized(&self) -> bool {
        self.current_block.is_none()
    }

    /// Create a generated block with an auto-incremented ID.
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
    /// Panics if no block has been activated.
    pub fn current_block(&self) -> BlockId {
        let idx = self.current_block.expect("no active block");
        self.blocks[idx].id
    }

    /// Emit an IR instruction into the currently active block.
    ///
    /// Creates a debugger group for the instruction so the backend can
    /// attach machine-level annotations to it.
    ///
    /// # Panics
    ///
    /// Panics if no block is active or if the block is finalized.
    pub fn emit(&mut self, inst: IrInst) {
        let idx = self.current_block.expect("emit: no active block");
        self.cb.dbg(|dbg| {
            dbg.record_ir_emit();
            dbg.set_source("operation", &format!("{inst}"));
        });
        self.blocks[idx].push(inst);
    }

    /// Get the VRegDef for a given VReg.
    pub fn vreg_def(&self, vreg: VReg) -> VRegDef {
        self.vreg_defs[vreg.0 as usize]
    }

    // --- Debug helpers ---

    /// Open a new source operation group with pc and label.
    ///
    /// Snapshots every vstack's current state into its debug column.
    pub fn begin_op(&mut self, pc: &str, label: &str) {
        let idx = self.current_block;
        let snapshots: Vec<(&str, String)> = self
            .vstack_configs
            .iter()
            .enumerate()
            .map(|(i, cfg)| {
                let state = idx.map(|b| &self.blocks[b].vstack_state[i]);
                (cfg.label, format_vstack_snapshot(state))
            })
            .collect();
        self.cb.dbg(|dbg| {
            dbg.set_pending("pc", pc);
            dbg.set_pending("label", label);
            for (label, snapshot) in &snapshots {
                dbg.set_pending(label, snapshot);
            }
        });
    }

    /// Allocate a temp VReg with no canonical stack slot.
    pub fn alloc_temp(&mut self, width: Width, value: Value) -> VReg {
        let id = VReg(self.next_vreg);
        self.next_vreg += 1;
        let remat = matches!(value, Value::ConstI32(_) | Value::ConstI64(_));
        self.vreg_defs.push(VRegDef {
            id,
            width,
            slot: None,
            value,
            remat,
        });
        self.record_def(id);
        id
    }

    /// Finalize — analyze control flow and produce the IRFunction.
    pub fn build(self) {
        let block_ids: Vec<BlockId> = self.blocks.iter().map(|bb| bb.id).collect();
        let proto_blocks: Vec<_> = self
            .blocks
            .into_iter()
            .enumerate()
            .map(|(i, bb)| {
                let mut successors = bb.successors;

                // Implicit fallthrough for non-finalized blocks.
                if successors.is_empty() && !bb.finalized {
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

        let all_params: Vec<Vec<VReg>> = proto_blocks
            .iter()
            .map(|(_, _, _, p, _)| p.clone())
            .collect();
        let all_ids: Vec<BlockId> = proto_blocks.iter().map(|(id, _, _, _, _)| *id).collect();

        let blocks = proto_blocks
            .into_iter()
            .map(|(id, defs, instructions, params, successors)| {
                let mut results = Vec::new();

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
            vstacks: self.vstack_configs,
            vreg_defs: self.vreg_defs,
            blocks,
        };

        self.cb.push_function(func);
    }

    // --- internal helpers ---

    /// Get a mutable reference to vstack state on the current block.
    fn vstack_mut(&mut self, vstack: VStackId) -> &mut VStackMut {
        let idx = self.current_block.expect("vstack_mut: no active block");
        &mut self.blocks[idx].vstack_state[vstack.0 as usize]
    }

    /// Get a shared reference to vstack state on the current block.
    fn vstack_ref(&self, vstack: VStackId) -> &VStackMut {
        let idx = self.current_block.expect("vstack_ref: no active block");
        &self.blocks[idx].vstack_state[vstack.0 as usize]
    }

    /// Clone the current block's vstack state onto a target block.
    ///
    /// If the target already has vstack state (from another incoming edge),
    /// this is a no-op — wasm guarantees balanced stacks, so the states match.
    fn snapshot_vstack_onto(&mut self, target: BlockId) {
        let src_idx = self.current_block.expect("snapshot: no active block");
        let dst_idx = self.ensure_block(target);
        if self.blocks[dst_idx].vstack_state.is_empty() {
            let state = self.blocks[src_idx].vstack_state.clone();
            self.blocks[dst_idx].vstack_state = state;
        }
    }

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

    fn alloc_vreg(&mut self, width: Width, slot: CanonSlot, value: Value) -> VReg {
        let id = VReg(self.next_vreg);
        self.next_vreg += 1;
        // VStack-allocated VRegs are NOT rematerializable — their register
        // contents may be overwritten by ALU results or call returns, making
        // the VRegDef's `value` field stale. Only temps (alloc_temp) can be
        // safely rematerialized.
        self.vreg_defs.push(VRegDef {
            id,
            width,
            slot: Some(slot),
            value,
            remat: false,
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

    fn push_typed(&mut self, vstack: VStackId, width: Width, value: Value) -> VReg {
        let cfg = &self.vstack_configs[vstack.0 as usize];
        let label = cfg.label;
        let base_offset = cfg.base_offset;

        let vs = self.vstack_ref(vstack);
        let index = vs.depth;
        let size = width.bytes() as u8;
        let byte_offset = base_offset + index * (size as u32);

        let slot = CanonSlot {
            vstack,
            index,
            byte_offset,
            size,
        };

        if let Value::VReg(src) = value {
            self.record_use(src);
        }

        let vreg = self.alloc_vreg(width, slot, value);
        self.record_def(vreg);

        let base = base_preg(self.vstack_configs[slot.vstack.0 as usize].base);
        self.emit(IrInst::Store {
            src: Operand::VReg(vreg, width),
            base,
            offset: slot.byte_offset,
        });
        let op = format!("{label}.push {vreg} = {value}");
        self.cb.dbg(|dbg| dbg.set_source("operation", &op));

        let vs = self.vstack_mut(vstack);
        let idx = index as usize;
        if idx < vs.slots.len() {
            vs.slots[idx] = Some(vreg);
        } else {
            vs.slots.push(Some(vreg));
        }
        vs.depth += 1;

        vreg
    }

    /// Pop the top value from a vstack, asserting it matches the expected width.
    pub fn pop(&mut self, vstack: VStackId, width: Width) -> VReg {
        let label = self.vstack_configs[vstack.0 as usize].label;
        let vs = self.vstack_mut(vstack);
        assert!(vs.depth > 0, "pop: vstack '{label}' is empty");
        vs.depth -= 1;
        let vreg = vs.slots[vs.depth as usize].expect("pop: slot not defined");
        let actual_width = self.vreg_defs[vreg.0 as usize].width;
        assert_eq!(
            actual_width, width,
            "pop: vstack '{label}' expected {width:?} but top is {actual_width:?}"
        );
        self.record_use(vreg);
        let def = &self.vreg_defs[vreg.0 as usize];
        let slot = def.slot.expect("pop on temp vreg (no slot)");
        let base = base_preg(self.vstack_configs[slot.vstack.0 as usize].base);
        self.emit(IrInst::Load {
            dst: Register::VReg(vreg, width),
            base,
            offset: slot.byte_offset,
        });
        let op = format!("{label}.pop {vreg}");
        self.cb.dbg(|dbg| dbg.set_source("operation", &op));
        vreg
    }
}

fn base_preg(reg: Register) -> PReg {
    match reg {
        Register::PReg(p, _) => p,
        Register::VReg(_, _) => panic!("vstack base must be a physical register"),
    }
}

/// Format a vstack's current slots as a space-separated list of VReg names.
fn format_vstack_snapshot(vs: Option<&VStackMut>) -> String {
    let Some(vs) = vs else { return String::new() };
    let mut parts = Vec::new();
    for slot in vs.slots.iter().take(vs.depth as usize) {
        match slot {
            Some(vreg) => parts.push(format!("{vreg}")),
            None => parts.push("_".into()),
        }
    }
    parts.join(" ")
}
