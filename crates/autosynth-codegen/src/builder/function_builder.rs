use autosynth_ir::{
    Abi, AluOp, BlockId, CanonSlot, FunctionIdx, FunctionSignature, IRFunction, IrBlock, IrInst,
    VInit, VReg, VRegDef, VRegion, VRegionId,
};
use autosynth_isa::{PReg, Width};

use super::block_builder::{BlockBuilder, VStackMut};
use super::code_builder::CodeBuilder;
use crate::debugger::{self, Align};

/// Incrementally builds an [`IRFunction`] by managing virtual regions, blocks,
/// and VReg allocation.
///
/// Vstack configuration (label, base register, offset) is immutable and
/// function-scoped. Vstack mutable state (depth, slot assignments) lives
/// on each [`BlockBuilder`]. Branch methods (`br`, `br_if`) clone the
/// current block's vstack state onto target blocks, and `start_block`
/// activates a block whose state was set by a prior branch.
pub struct FunctionBuilder<'a> {
    /// The code builder that collects finalized functions.
    cb: &'a mut CodeBuilder,

    /// The function's type signature and calling convention.
    signature: FunctionSignature,

    /// VReg definitions, indexed by VReg id.
    vreg_defs: Vec<VRegDef>,
    next_vreg: u32,

    /// Immutable region configurations (label, base, offset).
    regions: Vec<VRegion>,

    /// All block builders, indexed by position.
    blocks: Vec<BlockBuilder>,
    /// Index of the currently active block builder.
    current_block: Option<usize>,
    /// Next generated block ID (for suspend stubs, cold paths, etc.).
    next_gen_id: u32,
}

impl<'a> FunctionBuilder<'a> {
    /// Create an empty function builder.
    ///
    /// Registers standard source columns (pc, label) on the thread-local
    /// debugger if one is installed.
    pub fn new(cb: &'a mut CodeBuilder, signature: FunctionSignature) -> Self {
        debugger::dbg(|dbg| {
            dbg.add_source_column("pc", Align::Right);
            dbg.add_source_column("label", Align::Left);
        });

        Self {
            cb,
            signature,
            vreg_defs: Vec::new(),
            next_vreg: 0,
            regions: Vec::new(),
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
    pub fn define_region(&mut self, region: VRegion) -> VRegionId {
        let id = VRegionId(self.regions.len() as u32);
        debugger::dbg(|dbg| dbg.add_source_column(region.label, Align::Left));
        self.regions.push(region);
        // Initialize empty state on the current block.
        let idx = self.current_block.expect("define_region: no active block");
        self.blocks[idx]
            .vstack_state
            .push(VStackMut { slots: Vec::new() });
        id
    }

    /// Allocate a destination VReg with a canonical slot but don't push it.
    ///
    /// The caller is responsible for pushing via [`push_vreg`] after
    /// the instruction that produces the value is emitted.
    pub fn alloc_dst(&mut self, vstack: VRegionId, width: Width) -> VReg {
        let index = self.vstack_ref(vstack).slots.len();
        let slot = self.make_slot(vstack, index, width);
        let vreg = self.alloc_vreg(width, slot, None);
        self.record_def(vreg);
        vreg
    }

    /// Append a new field to a region, initialized from a VReg.
    ///
    /// Width is inferred from the VReg's definition. Byte offset is computed
    /// by summing the sizes of all preceding fields.
    pub fn define_field(&mut self, region: VRegionId, vreg: VReg) {
        let w = self.vreg_defs[vreg.0 as usize].width;
        let index = self.vstack_ref(region).slots.len();
        let slot = self.make_slot(region, index, w);

        // Give the vreg a canonical slot if it doesn't have one.
        if self.vreg_defs[vreg.0 as usize].slot.is_none() {
            self.vreg_defs[vreg.0 as usize].slot = Some(slot);
        }

        let label = self.regions[region.0 as usize].label;
        let desc = self.fmt_vreg(vreg);
        debugger::dbg(|dbg| dbg.note(&format!("{label}[{index}] ← {desc}")));

        self.vstack_mut(region).slots.push(vreg);
    }

    /// Read a field from a region by index.
    ///
    /// Allocates a new VReg with `CopyOf` — the caller may hold this value
    /// while the field gets overwritten by a later `set_field`.
    pub fn get_field(&mut self, region: VRegionId, index: usize) -> VReg {
        let src = self.vstack_ref(region).slots[index];
        let w = self.vreg_defs[src.0 as usize].width;
        let copy = self.alloc_temp(w, Some(VInit::CopyOf(src)));
        self.record_use(src);
        copy
    }

    /// Write a VReg value to a region field, replacing its current value.
    ///
    /// Sets the vreg's canonical slot to the field's location. Asserts
    /// the width matches the existing field — changing a slot's size is illegal.
    pub fn set_field(&mut self, region: VRegionId, index: usize, vreg: VReg) {
        let w = self.vreg_defs[vreg.0 as usize].width;
        let existing_vreg = self.vstack_ref(region).slots[index];
        let existing_slot = self.vreg_defs[existing_vreg.0 as usize]
            .slot
            .expect("set_field: existing field has no canonical slot");
        assert_eq!(
            existing_slot.size,
            w.bytes() as u8,
            "set_field: cannot change field size from {} to {}",
            existing_slot.size,
            w.bytes()
        );

        // Update the vreg's canonical slot to this field's location.
        self.vreg_defs[vreg.0 as usize].slot = Some(existing_slot);

        let label = self.regions[region.0 as usize].label;
        let desc = self.fmt_vreg(vreg);
        debugger::dbg(|dbg| dbg.note(&format!("{label}[{index}] ← {desc}")));

        self.vstack_mut(region).slots[index] = vreg;
    }

    /// Get the current slot count of a region.
    pub fn stack_depth(&self, vstack: VRegionId) -> u32 {
        self.vstack_ref(vstack).slots.len() as u32
    }

    // --- Block lifecycle ---

    /// Set the entry block and register the "operation" source column.
    ///
    /// Must be called before `define_vstack` since vstacks initialize
    /// state on the current block.
    pub fn entry_block(&mut self, block: BlockId) {
        let idx = self.ensure_block(block);
        self.current_block = Some(idx);
        debugger::dbg(|dbg| dbg.mark_block_start(block));
    }

    /// Finish vstack definitions and register the "operation" column.
    ///
    /// Call this after all `define_vstack` calls and before emitting
    /// instructions, so the operation column appears rightmost.
    pub fn finish_entry(&mut self) {
        debugger::dbg(|dbg| dbg.add_source_column("operation", Align::Left));
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
        debugger::dbg(|dbg| dbg.mark_block_start(block));
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
    /// Emits a `BrIf` that consumes flags from a preceding `Alu(Comp)`.
    /// Clones the current block's vstack state onto both targets.
    pub fn br_if(&mut self, cond: VReg, block_if: BlockId, block_else: BlockId) {
        let idx = self.current_block.expect("br_if: no active block");

        let inst = IrInst::BrIf {
            cond,
            block_if,
            block_else,
        };
        debugger::dbg(|dbg| {
            dbg.record_ir_emit();
            dbg.set_source("operation", &format!("{inst}"));
        });
        self.blocks[idx].push(inst);

        self.snapshot_vstack_onto(block_if);
        self.snapshot_vstack_onto(block_else);
        self.blocks[idx].successors.push(block_if);
        self.blocks[idx].successors.push(block_else);
        self.blocks[idx].finalized = true;
        self.current_block = None;
    }

    /// Raw return — finalizes the current block (no successors).
    ///
    /// Does NOT pop results into calling convention registers.
    /// Prefer [`emit_return`](Self::emit_return) which handles
    /// the ABI automatically.
    pub fn ret(&mut self) {
        self.emit(IrInst::Return);
        let idx = self.current_block.expect("ret: no active block");
        self.blocks[idx].finalized = true;
        self.current_block = None;
    }

    /// Pop results, move into calling convention registers, and emit a return.
    ///
    /// Under [`Abi::NativeWasm`], results are popped from the operand
    /// vstack and moved into CC registers (PReg(0), PReg(1), ...) in
    /// reverse order (top of stack = last result).
    ///
    /// Under [`Abi::StackWasm`], results are already on the canonical
    /// stack — no register moves needed.
    pub fn emit_return(&mut self, operands: VRegionId) {
        match self.signature.abi {
            Abi::NativeWasm => {
                let n = self.signature.results.len();
                for (i, ty) in self.signature.results.clone().iter().enumerate() {
                    let vreg = self.peek(operands, n - 1 - i);
                    assert_eq!(
                        self.vreg_defs[vreg.0 as usize].width,
                        ty.width(),
                        "emit_return: result {i} width mismatch"
                    );
                    self.set_target(vreg, PReg(i as u8));
                }
                self.drop_n(operands, n);
            }
            Abi::StackWasm => {}
        }
        self.ret();
    }

    /// Pop args, emit a call, and push results per the callee's ABI.
    ///
    /// Under [`Abi::NativeWasm`], arguments are popped from the operand
    /// vstack and moved into CC registers (PReg(0), PReg(1), ...) in
    /// reverse order, the call is emitted, and results are pushed back
    /// from the same CC registers.
    ///
    /// # Panics
    ///
    /// Panics if no signature is registered for `func_idx`.
    pub fn emit_call(
        &mut self,
        operands: VRegionId,
        func_idx: FunctionIdx,
        frame_advance: u32,
        lbp: VReg,
    ) {
        let callee_sig = self
            .cb
            .signature(&func_idx)
            .unwrap_or_else(|| panic!("emit_call: no signature for {func_idx}"))
            .clone();

        match callee_sig.abi {
            Abi::NativeWasm => {
                // Set target CC registers on the arg VRegs already on the stack.
                let n = callee_sig.params.len();
                for (i, ty) in callee_sig.params.iter().enumerate() {
                    let vreg = self.peek(operands, n - 1 - i);
                    assert_eq!(
                        self.vreg_defs[vreg.0 as usize].width,
                        ty.width(),
                        "emit_call: arg {i} width mismatch"
                    );
                    self.set_target(vreg, PReg(i as u8));
                }
                // Soft-drop args — consumed by the call, no IR emitted.
                self.drop_n(operands, n);
            }
            Abi::StackWasm => {}
        }

        // Frame advance: add lbp, lbp, #frame_advance
        if frame_advance > 0 {
            let advance = self.const_i32(frame_advance as i32);
            self.emit(IrInst::Alu {
                op: AluOp::Add,
                dst: lbp,
                lhs: lbp,
                rhs: advance,
            });
        }

        self.emit(IrInst::Call { func_idx });

        self.begin_op("--", "restore frame");

        // Frame restore: sub lbp, lbp, #frame_advance
        if frame_advance > 0 {
            let advance = self.const_i32(frame_advance as i32);
            self.emit(IrInst::Alu {
                op: AluOp::Sub,
                dst: lbp,
                lhs: lbp,
                rhs: advance,
            });
        }

        match callee_sig.abi {
            Abi::NativeWasm => {
                // Push fresh VRegs for results — initialized from CC registers.
                for (i, ty) in callee_sig.results.iter().enumerate() {
                    let v = self.preg_vreg(PReg(i as u8), ty.width());
                    self.push_vreg(operands, v);
                }
            }
            Abi::StackWasm => {}
        }
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
        debugger::dbg(|dbg| {
            dbg.record_ir_emit();
            dbg.set_source("operation", &format!("{inst}"));
        });
        self.blocks[idx].push(inst);
    }

    /// Get the VRegDef for a given VReg.
    pub fn vreg_def(&self, vreg: VReg) -> VRegDef {
        self.vreg_defs[vreg.0 as usize]
    }

    /// Format a VReg with its type and initializer for debug display.
    fn fmt_vreg(&self, vreg: VReg) -> String {
        format_vreg(vreg, &self.vreg_defs)
    }

    /// Set a register placement constraint on a VReg.
    ///
    /// Constrain a VReg to a specific physical register.
    ///
    /// The allocator must place this VReg in the given physical register,
    /// evicting the current occupant if necessary. Used for calling
    /// convention constraints.
    pub fn set_target(&mut self, vreg: VReg, target: PReg) {
        self.vreg_defs[vreg.0 as usize].target = Some(target);
    }

    // --- Debug helpers ---

    /// Open a new source operation group with pc and label.
    ///
    /// Snapshots every vstack's current state into its debug column.
    pub fn begin_op(&mut self, pc: &str, label: &str) {
        let idx = self.current_block;
        let snapshots: Vec<(&str, String)> = self
            .regions
            .iter()
            .enumerate()
            .map(|(i, cfg)| {
                let state = idx.map(|b| &self.blocks[b].vstack_state[i]);
                (cfg.label, format_vstack_snapshot(state, &self.vreg_defs))
            })
            .collect();
        debugger::dbg(|dbg| {
            dbg.set_pending("pc", pc);
            dbg.set_pending("label", label);
            for (label, snapshot) in &snapshots {
                dbg.set_pending(label, snapshot);
            }
        });
    }

    /// Allocate a temp constant i32 VReg — no canonical slot, rematerializable.
    pub fn const_i32(&mut self, val: i32) -> VReg {
        self.alloc_temp(Width::W32, Some(VInit::Const(val as i64)))
    }

    /// Allocate a temp constant i64 VReg — no canonical slot, rematerializable.
    pub fn const_i64(&mut self, val: i64) -> VReg {
        self.alloc_temp(Width::W64, Some(VInit::Const(val)))
    }

    /// Allocate a temp VReg initialized from a physical register.
    ///
    /// Used for function parameters that arrive in calling convention registers.
    pub fn preg_vreg(&mut self, preg: PReg, width: Width) -> VReg {
        self.alloc_temp(width, Some(VInit::PReg(preg)))
    }

    /// Push a constant i32 onto a region.
    pub fn push_const_i32(&mut self, region: VRegionId, val: i32) {
        let v = self.const_i32(val);
        self.push_vreg(region, v);
    }

    /// Push an existing VReg onto a region's stack. No new vreg allocated.
    pub fn push_vreg(&mut self, region: VRegionId, vreg: VReg) {
        let label = self.regions[region.0 as usize].label;
        let desc = self.fmt_vreg(vreg);
        debugger::dbg(|dbg| dbg.note(&format!("{label} ← {desc}")));
        self.vstack_mut(region).slots.push(vreg);
    }

    /// Pop the top value from a region — width inferred from the vreg def.
    pub fn pop_any(&mut self, region: VRegionId) -> VReg {
        let label = self.regions[region.0 as usize].label;
        let vreg = self
            .vstack_mut(region)
            .slots
            .pop()
            .unwrap_or_else(|| panic!("pop_any: vstack '{label}' is empty"));
        self.record_use(vreg);
        let desc = self.fmt_vreg(vreg);
        debugger::dbg(|dbg| dbg.note(&format!("{label} → {desc}")));
        vreg
    }

    /// Pop two operands, push a destination, emit an Alu instruction.
    ///
    /// Returns the destination VReg. Width is inferred from the popped operands.
    pub fn binop(&mut self, op: AluOp, region: VRegionId) -> VReg {
        let rhs = self.pop_any(region);
        let lhs = self.pop_any(region);
        let w = self.vreg_defs[lhs.0 as usize].width;
        let dst = self.alloc_dst(region, w);
        self.emit(IrInst::Alu { op, dst, lhs, rhs });
        self.push_vreg(region, dst);
        dst
    }

    /// Allocate a temp VReg with no canonical stack slot.
    pub fn alloc_temp(&mut self, width: Width, initial: Option<VInit>) -> VReg {
        let id = VReg(self.next_vreg);
        self.next_vreg += 1;

        self.vreg_defs.push(VRegDef {
            id,
            width,
            slot: None,
            initial,
            target: None,
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

                IrBlock {
                    id,
                    params,
                    results,
                    successors,
                    instructions,
                }
            })
            .collect::<Vec<_>>();

        // Fallthrough elimination: wrap trailing Branch instructions
        // whose target is the immediately following block in Skipped.
        // We keep the instruction in the list so ir_index stays aligned
        // with debugger groups.
        let mut blocks = blocks;
        for i in 0..blocks.len() {
            let next_id = blocks.get(i + 1).map(|b| b.id);
            if let Some(IrInst::Branch { target }) = blocks[i].instructions.last() {
                if Some(*target) == next_id {
                    let inst = blocks[i].instructions.pop().unwrap();
                    blocks[i].instructions.push(IrInst::Skipped(Box::new(inst)));
                }
            }
        }

        let func = IRFunction {
            regions: self.regions,
            vreg_defs: self.vreg_defs,
            blocks,
        };

        for block in &func.blocks {
            let params: Vec<String> = block
                .params
                .iter()
                .map(|vreg| {
                    let def = &func.vreg_defs[vreg.0 as usize];
                    format!("{}<{}>", vreg, def.width)
                })
                .collect();
            let results: Vec<String> = block
                .results
                .iter()
                .map(|vreg| {
                    let def = &func.vreg_defs[vreg.0 as usize];
                    format!("{}<{}>", vreg, def.width)
                })
                .collect();
            debugger::dbg(|dbg| dbg.set_block_meta(block.id, params, results));
        }

        self.cb.push_function(func);
    }

    // --- internal helpers ---

    /// Get a mutable reference to vstack state on the current block.
    fn vstack_mut(&mut self, vstack: VRegionId) -> &mut VStackMut {
        let idx = self.current_block.expect("vstack_mut: no active block");
        &mut self.blocks[idx].vstack_state[vstack.0 as usize]
    }

    /// Get a shared reference to vstack state on the current block.
    fn vstack_ref(&self, vstack: VRegionId) -> &VStackMut {
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

    /// Build a canonical slot for a new field at `index` in `region`.
    ///
    /// Byte offset is computed by summing the sizes of all preceding fields.
    fn make_slot(&self, region: VRegionId, index: usize, width: Width) -> CanonSlot {
        let base_offset = self.regions[region.0 as usize].base_offset;
        let size = width.bytes() as u8;

        // Sum sizes of preceding slots to get byte offset.
        let vs = self.vstack_ref(region);
        let preceding_bytes: u32 = vs
            .slots
            .iter()
            .take(index)
            .map(|v| self.vreg_defs[v.0 as usize].width.bytes() as u32)
            .sum();

        CanonSlot {
            region,
            index: index as u32,
            byte_offset: base_offset + preceding_bytes,
            size,
        }
    }

    fn alloc_vreg(&mut self, width: Width, slot: CanonSlot, initial: Option<VInit>) -> VReg {
        let id = VReg(self.next_vreg);
        self.next_vreg += 1;
        self.vreg_defs.push(VRegDef {
            id,
            width,
            slot: Some(slot),
            initial,
            target: None,
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


    /// Peek at a vstack slot by offset from the top (0 = top, 1 = second from top).
    ///
    /// Returns the VReg without modifying the vstack. Used by `emit_call`
    /// and `emit_return` to inspect operands before soft-dropping them.
    pub fn peek(&self, vstack: VRegionId, offset_from_top: usize) -> VReg {
        let label = self.regions[vstack.0 as usize].label;
        let vs = self.vstack_ref(vstack);
        let len = vs.slots.len();
        assert!(
            offset_from_top < len,
            "peek: offset {offset_from_top} out of bounds (depth={len}) on vstack '{label}'"
        );
        vs.slots[len - 1 - offset_from_top]
    }

    /// Drop the top N values from a vstack without emitting any IR.
    ///
    /// Used after `peek` + `set_target` to consume args that are handed
    /// off to a call — the values are "consumed" at the IR level but no
    /// load/store instructions are needed.
    pub fn drop_n(&mut self, vstack: VRegionId, n: usize) {
        let label = self.regions[vstack.0 as usize].label;
        let vs = self.vstack_mut(vstack);
        assert!(
            n <= vs.slots.len(),
            "drop_n: dropping {n} but vstack '{label}' depth is {}",
            vs.slots.len()
        );
        vs.slots.truncate(vs.slots.len() - n);
    }

    /// Pop the top value from a vstack, asserting it matches the expected width.
    ///
    /// Pure bookkeeping — decrements depth and returns the vreg.
    /// No IR instructions emitted. The vreg keeps its canonical slot
    /// so the orchestrator can reload it if needed.
    pub fn pop(&mut self, vstack: VRegionId, width: Width) -> VReg {
        let label = self.regions[vstack.0 as usize].label;
        let vreg = self
            .vstack_mut(vstack)
            .slots
            .pop()
            .unwrap_or_else(|| panic!("pop: vstack '{label}' is empty"));
        let actual_width = self.vreg_defs[vreg.0 as usize].width;
        assert_eq!(
            actual_width, width,
            "pop: vstack '{label}' expected {width:?} but top is {actual_width:?}"
        );
        self.record_use(vreg);
        let desc = self.fmt_vreg(vreg);
        debugger::dbg(|dbg| dbg.note(&format!("{label} → {desc}")));
        vreg
    }
}

/// Format a single VReg with its type and initializer info.
///
/// Examples: `v0=i32` (no known value), `v1=0:i32` (const 0),
/// `v2=p0:i32` (from PReg 0), `v3=v1:i32` (copy of v1).
fn format_vreg(vreg: VReg, defs: &[VRegDef]) -> String {
    let def = &defs[vreg.0 as usize];
    let ty = match def.width {
        Width::W32 => "i32",
        Width::W64 => "i64",
    };
    match def.initial {
        Some(VInit::Const(n)) => format!("{vreg}={n}:{ty}"),
        Some(VInit::PReg(p)) => format!("{vreg}=p{}:{ty}", p.0),
        Some(VInit::CopyOf(src)) => format!("{vreg}={src}:{ty}"),
        None => format!("{vreg}={ty}"),
    }
}

/// Format a vstack's current slots with type and value info.
fn format_vstack_snapshot(vs: Option<&VStackMut>, defs: &[VRegDef]) -> String {
    let Some(vs) = vs else { return String::new() };
    vs.slots
        .iter()
        .map(|vreg| format_vreg(*vreg, defs))
        .collect::<Vec<_>>()
        .join(" ")
}
