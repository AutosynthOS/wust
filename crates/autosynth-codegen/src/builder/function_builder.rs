use std::collections::{HashMap, HashSet};

use autosynth_ir::{
    Abi, AluOp, BlockId, FunctionSignature, IrInst, LowerInst, RegInst, SlotRef, VInit, VReg,
    VRegDef, VRegRef, VRegRefSource, VRegion, VRegionId, resolve_ref,
};
use autosynth_isa::{PReg, Width};
use autosynth_lower::{trace, trace_ctx, trace_do};

use super::code_builder::CodeBuilder;
use crate::ir_function::{IRFunction, IrBlock};


/// Incrementally builds an [`IRFunction`] by emitting instructions
/// into blocks and managing VReg allocation.
pub struct FunctionBuilder<'a> {
    /// The code builder that collects finalized functions.
    cb: &'a mut CodeBuilder,

    /// Machine configuration (register pool, reservations).
    config: autosynth_lower::MachineConfig,

    /// The function's type signature and calling convention.
    signature: FunctionSignature,

    /// Virtual region configurations.
    pub regions: Vec<VRegion>,

    /// Per-def metadata, indexed by Def id.
    vreg_defs: Vec<VRegDef>,
    /// Next def id for allocation.
    next_vreg: u32,

    /// Per-ref metadata, indexed by Ref id.
    vreg_refs: Vec<VRegRef>,
    /// Next ref id for allocation.
    next_ref: u32,

    /// Block layout order.
    block_order: Vec<BlockId>,
    /// All blocks, keyed by BlockId.
    blocks: HashMap<BlockId, IrBlock>,
    /// The currently active block.
    current_block: Option<BlockId>,
    /// Next generated block ID (for suspend stubs, cold paths, etc.).
    next_gen_id: u32,

    /// Region snapshots saved at branch points, keyed by target block.
    /// Accumulates one snapshot per predecessor for merge detection.
    region_snapshots: HashMap<BlockId, Vec<(BlockId, Vec<VRegion>)>>,
}

impl<'a> FunctionBuilder<'a> {
    pub fn new(
        cb: &'a mut CodeBuilder,
        config: autosynth_lower::MachineConfig,
        signature: FunctionSignature,
    ) -> Self {
        Self {
            cb,
            config,
            signature,
            regions: Vec::new(),
            vreg_defs: Vec::new(),
            next_vreg: 0,
            vreg_refs: Vec::new(),
            next_ref: 0,
            block_order: Vec::new(),
            blocks: HashMap::new(),
            current_block: None,
            next_gen_id: 0,
            region_snapshots: HashMap::new(),
        }
    }

    // --- Def/use tracking ---

    fn record_def(&mut self, vreg: VReg) {
        if let Some(id) = self.current_block {
            self.blocks.get_mut(&id).unwrap().defs.insert(vreg);
        }
    }

    fn record_use(&mut self, vreg: VReg) {
        if let Some(id) = self.current_block {
            self.blocks.get_mut(&id).unwrap().uses.insert(vreg);
        }
    }

    // --- Region operations ---

    /// Compute the byte offset of a slot within a region.
    ///
    /// Sums the widths (in bytes) of all slots preceding `index`,
    /// then adds the region's base_offset.
    fn slot_offset(&self, region: VRegionId, index: u32) -> SlotRef {
        let r = &self.regions[region.0 as usize];
        let mut offset = r.base_offset;
        for i in 0..index as usize {
            let vreg = r.slots[i];
            offset += self.vreg_width(vreg).bytes();
        }
        SlotRef {
            base: r.base,
            offset,
        }
    }

    /// Register a new virtual region.
    pub fn define_region(&mut self, region: VRegion) -> VRegionId {
        let id = VRegionId(self.regions.len() as u32);
        self.regions.push(region);
        id
    }

    /// Push a vreg onto a region. Emits `RegInst::SetSlot`.
    pub fn push_vreg(&mut self, region: VRegionId, vreg: VReg) {
        self.record_use(vreg);
        let index = self.regions[region.0 as usize].slots.len() as u32;
        let slot = self.slot_offset(region, index);
        self.regions[region.0 as usize].slots.push(vreg);
        self.emit_reg(RegInst::SetSlot { vreg, slot });
    }

    /// Pop the top vreg from a region. Asserts the vreg's width matches
    /// `expected`. Emits `RegInst::ClearSlot`.
    pub fn pop(&mut self, region: VRegionId, expected: Width) -> VReg {
        let index = self.regions[region.0 as usize].slots.len() as u32 - 1;
        let slot = self.slot_offset(region, index);
        let vreg = self.regions[region.0 as usize]
            .slots
            .pop()
            .expect("pop: region is empty");
        let actual = self.vreg_width(vreg);
        assert_eq!(
            actual, expected,
            "pop: expected {expected} but vreg {vreg} is {actual}"
        );
        self.record_use(vreg);
        self.emit_reg(RegInst::ClearSlot { vreg, slot });
        vreg
    }

    /// Emit Clobber for every vreg in a region. Used before calls to
    /// ensure all values are stored to memory.
    pub fn clobber_region(&mut self, region: VRegionId) {
        for vreg in self.regions[region.0 as usize].slots.clone() {
            self.emit_reg(RegInst::Clobber { vreg });
        }
    }

    /// Read a field from a region by index.
    pub fn get_field(&mut self, region: VRegionId, index: usize) -> VReg {
        let vreg = self.regions[region.0 as usize].slots[index];
        self.record_use(vreg);
        vreg
    }

    /// Write a vreg into an existing region slot. Emits `RegInst::SetSlot`.
    pub fn set_field(&mut self, region: VRegionId, index: usize, vreg: VReg) {
        self.record_use(vreg);
        let slot = self.slot_offset(region, index as u32);
        // Clear the old occupant's slot association before overwriting.
        let old = self.regions[region.0 as usize].slots[index];
        if old != vreg {
            self.emit_reg(RegInst::ClearSlot { vreg: old, slot });
        }
        self.regions[region.0 as usize].slots[index] = vreg;
        self.emit_reg(RegInst::SetSlot { vreg, slot });
    }

    // --- VReg allocation ---

    /// Allocate a new vreg with the given width and origin.
    ///
    /// Emits a `RegInst::Define` so the lowerer knows about the vreg
    /// and its initial value origin.
    pub fn alloc_vreg(&mut self, width: Width, origin: VInit) -> VReg {
        let id = VReg::Def(self.next_vreg);
        self.next_vreg += 1;
        self.vreg_defs.push(VRegDef {
            id,
            width,
            target: None,
        });
        self.record_def(id);
        self.emit_reg(RegInst::Define { vreg: id, value: origin });
        id
    }

    /// Allocate a new ref vreg with the given width and source.
    fn alloc_ref(&mut self, width: Width, source: VRegRefSource) -> VReg {
        let id = VReg::Ref(self.next_ref);
        self.next_ref += 1;
        self.vreg_refs.push(VRegRef {
            id,
            width,
            source,
        });
        id
    }

    /// Get the width of a vreg (any kind).
    pub fn vreg_width(&self, vreg: VReg) -> Width {
        match vreg {
            VReg::Def(id) => self.vreg_defs[id as usize].width,
            VReg::Ref(id) => self.vreg_refs[id as usize].width,
        }
    }

    /// Set the target physical register for a vreg.
    ///
    /// For Ref VRegs, propagates the target to the underlying source.
    pub fn set_target(&mut self, vreg: VReg, preg: PReg) {
        self.record_use(vreg);
        match vreg {
            VReg::Def(id) => self.vreg_defs[id as usize].target = Some(preg),
            VReg::Ref(id) => {
                let source = &self.vreg_refs[id as usize].source;
                match source {
                    VRegRefSource::Direct(src) => self.set_target(*src, preg),
                    VRegRefSource::Phi(sources) => {
                        let sources = sources.clone();
                        for (_, src) in &sources {
                            self.set_target(*src, preg);
                        }
                    }
                }
            }
        }
    }

    // --- Block lifecycle ---

    pub fn entry_block(&mut self, block: BlockId) {
        self.ensure_block(block);
        self.current_block = Some(block);
        trace_ctx!("block", format!("{block:?}"));
        trace!({"type": "block_start", "block": format!("{block:?}")});
    }

    pub fn start_block(&mut self, block: BlockId) {
        self.ensure_block(block);
        self.current_block = Some(block);
        let snapshots = self.region_snapshots.remove(&block).unwrap_or_default();

        if let Some(first) = snapshots.first() {
            self.regions = first.1.clone();
            self.wrap_region_slots_in_refs(&snapshots);
        }
        trace_ctx!("block", format!("{block:?}"));
        trace!({"type": "block_start", "block": format!("{block:?}")});
    }

    /// Replace each region slot with a Ref vreg.
    ///
    /// For slots that already hold a Ref, keep as-is.
    /// For Defs, wrap in a Direct ref (single predecessor) or
    /// diff across all predecessors to decide Direct vs Phi.
    fn wrap_region_slots_in_refs(
        &mut self,
        snapshots: &[(BlockId, Vec<VRegion>)],
    ) {
        for region_idx in 0..self.regions.len() {
            for slot_idx in 0..self.regions[region_idx].slots.len() {
                let slot = self.regions[region_idx].slots[slot_idx];
                if matches!(slot, VReg::Ref(_)) {
                    continue;
                }

                let width = self.vreg_width(slot);
                let source = self.merge_slot(snapshots, region_idx, slot_idx);
                let is_phi = matches!(source, VRegRefSource::Phi(_));
                let ref_vreg = self.alloc_ref(width, source);
                self.regions[region_idx].slots[slot_idx] = ref_vreg;

                // Phi refs need converge_into to materialize them, which
                // requires them to be params. Record usage so they appear
                // in uses \ defs even if no instruction explicitly touches them.
                if is_phi {
                    self.record_use(ref_vreg);
                }
            }
        }
    }

    /// Determine the VRegRefSource for a single region slot across
    /// all predecessor snapshots.
    ///
    /// If every predecessor has the same root vreg at this position,
    /// returns Direct. Otherwise returns Phi with per-predecessor sources.
    fn merge_slot(
        &self,
        snapshots: &[(BlockId, Vec<VRegion>)],
        region_idx: usize,
        slot_idx: usize,
    ) -> VRegRefSource {
        let refs = &self.vreg_refs;
        let first_root = resolve_ref(snapshots[0].1[region_idx].slots[slot_idx], refs);

        let all_same = snapshots.iter().all(|(_, regions)| {
            resolve_ref(regions[region_idx].slots[slot_idx], refs) == first_root
        });

        if all_same {
            VRegRefSource::Direct(first_root)
        } else {
            let sources = snapshots
                .iter()
                .map(|(pred_block, regions)| {
                    (*pred_block, resolve_ref(regions[region_idx].slots[slot_idx], refs))
                })
                .collect();
            VRegRefSource::Phi(sources)
        }
    }

    pub fn br(&mut self, target: BlockId) {
        self.emit(IrInst::Branch { target });
        self.snapshot_regions_onto(target);
        let id = self.current_block.expect("br: no active block");
        let block = self.blocks.get_mut(&id).unwrap();
        block.successors.push(target);
        block.finalized = true;
        self.current_block = None;
    }

    pub fn br_if(&mut self, cond: VReg, block_if: BlockId, block_else: BlockId) {
        let id = self.current_block.expect("br_if: no active block");

        let inst = IrInst::BrIf {
            cond,
            block_if,
            block_else,
        };

        trace_do! {
            let seq = autosynth_lower::trace::next_seq();
            let inst_json = autosynth_lower::__serde_json::to_value(&inst).unwrap();
            trace!({
                "type": "ir",
                "seq": seq,
                "inst": inst_json
            });
        }

        let block = self.blocks.get_mut(&id).unwrap();
        assert!(
            !block.finalized,
            "cannot emit into finalized block {:?}",
            id
        );
        block.instructions.push(LowerInst::Ir(inst));

        self.snapshot_regions_onto(block_if);
        self.snapshot_regions_onto(block_else);
        let block = self.blocks.get_mut(&id).unwrap();
        block.successors.push(block_if);
        block.successors.push(block_else);
        block.finalized = true;
        self.current_block = None;
    }

    pub fn ret(&mut self) {
        self.emit(IrInst::Return);
        let id = self.current_block.expect("ret: no active block");
        let block = self.blocks.get_mut(&id).unwrap();
        block.finalized = true;
        self.current_block = None;
    }

    pub fn is_finalized(&self) -> bool {
        self.current_block.is_none()
    }

    pub fn gen_block(&mut self) -> BlockId {
        let id = BlockId::Gen(self.next_gen_id);
        self.next_gen_id += 1;
        self.ensure_block(id);
        id
    }

    /// Emit an IR instruction into the currently active block.
    pub fn emit(&mut self, inst: IrInst) {
        let id = self.current_block.expect("emit: no active block");

        trace_do! {
            let seq = autosynth_lower::trace::next_seq();
            let inst_json = autosynth_lower::__serde_json::to_value(&inst).unwrap();
            trace!({
                "type": "ir",
                "seq": seq,
                "inst": inst_json
            });
        }

        let block = self.blocks.get_mut(&id).unwrap();
        assert!(
            !block.finalized,
            "cannot emit into finalized block {:?}",
            id
        );
        block.instructions.push(LowerInst::Ir(inst));
    }

    /// Emit a register allocation instruction into the currently active block.
    pub fn emit_reg(&mut self, inst: RegInst) {
        let id = self.current_block.expect("emit_reg: no active block");
        let block = self.blocks.get(&id).unwrap();
        assert!(
            !block.finalized,
            "cannot emit into finalized block {:?}",
            id
        );

        trace_do! {
            let seq = autosynth_lower::trace::next_seq();
            let inst_json = autosynth_lower::__serde_json::to_value(&inst).unwrap();
            let regions: Vec<_> = self.regions.iter().map(|r| {
                autosynth_lower::__serde_json::json!({
                    "label": r.label,
                    "slots": r.slots.iter().map(|v| autosynth_lower::__serde_json::to_value(v).unwrap()).collect::<Vec<_>>()
                })
            }).collect();
            trace!({
                "type": "reg",
                "seq": seq,
                "inst": inst_json,
                "regions": regions
            });
        }

        let block = self.blocks.get_mut(&id).unwrap();
        block.instructions.push(LowerInst::Reg(inst));
    }

    pub fn binop(&mut self, op: AluOp, region: VRegionId, width: Width) {
        let rhs = self.pop(region, width);
        let lhs = self.pop(region, width);
        let w = width;
        let dst = self.alloc_vreg(w, VInit::InstDst);
        self.emit(IrInst::Alu { op, dst, lhs, rhs });
        self.push_vreg(region, dst);
    }

    /// Finalize — produce the IRFunction.
    pub fn build(self) {
        trace_do! {
            let defs_json = autosynth_lower::__serde_json::to_value(&self.vreg_defs).unwrap();
            let refs_json = autosynth_lower::__serde_json::to_value(&self.vreg_refs).unwrap();
            let regions_json = autosynth_lower::__serde_json::to_value(&self.regions).unwrap();
            trace!({
                "type": "build_end",
                "vreg_defs": defs_json,
                "vreg_refs": refs_json,
                "regions": regions_json
            });
        }

        let block_order = rpo(&self.block_order[0], &self.blocks);
        let mut blocks = self.blocks;
        let vreg_defs = self.vreg_defs;
        let vreg_refs = self.vreg_refs;

        // Compute params: uses that aren't defs (must come from predecessors).
        for id in &block_order {
            let block = blocks.get_mut(id).unwrap();
            block.params = block.uses.difference(&block.defs).copied().collect();
        }

        // Compute results: vregs that must stay live at this block's exit
        // because a successor needs them.
        //
        // Successor params may be Ref VRegs. Resolve them to find which
        // Def this specific predecessor is responsible for:
        //   - Direct ref → resolve to the underlying Def
        //   - Phi ref → find the source for THIS predecessor block
        for id in &block_order {
            let successors = blocks[id].successors.clone();
            let mut results = HashSet::new();
            for succ_id in &successors {
                if let Some(succ) = blocks.get(succ_id) {
                    for &param in &succ.params {
                        let needed = match param {
                            VReg::Def(_) => param,
                            VReg::Ref(ref_id) => {
                                match &vreg_refs[ref_id as usize].source {
                                    VRegRefSource::Direct(src) => *src,
                                    VRegRefSource::Phi(sources) => {
                                        // Find the source VReg for this predecessor.
                                        match sources.iter().find(|(pred, _)| pred == id) {
                                            Some((_, src)) => *src,
                                            None => continue,
                                        }
                                    }
                                }
                            }
                        };
                        let block = &blocks[id];
                        if block.defs.contains(&needed) || block.uses.contains(&needed) {
                            results.insert(needed);
                        }
                    }
                }
            }
            blocks.get_mut(id).unwrap().results = results;
        }

        // Compute remaining_uses per block: count how many times each
        // vreg (resolved to Def) is referenced. Vregs in results get
        // usize::MAX (done last to avoid wrapping).
        for id in &block_order {
            let block = blocks.get_mut(id).unwrap();
            let mut remaining = HashMap::new();

            for inst in block.instructions.iter() {
                let mut mark = |vreg: VReg| {
                    let resolved = resolve_ref(vreg, &vreg_refs);
                    *remaining.entry(resolved).or_insert(0usize) += 1;
                };
                match inst {
                    LowerInst::Ir(ir) => match ir {
                        IrInst::Alu { lhs, rhs, .. } => { mark(*lhs); mark(*rhs); }
                        IrInst::BrIf { cond, .. } => { mark(*cond); }
                        _ => {}
                    },
                    LowerInst::Reg(reg) => match reg {
                        RegInst::SetSlot { vreg, .. }
                        | RegInst::ClearSlot { vreg, .. }
                        | RegInst::Clobber { vreg }
                        | RegInst::Resolve { vreg } => { mark(*vreg); }
                        RegInst::Define { .. } => {}
                    },
                }
            }

            for &vreg in &block.results {
                let resolved = resolve_ref(vreg, &vreg_refs);
                remaining.insert(resolved, usize::MAX);
            }

            block.remaining_uses = remaining;
        }

        // Implicit fallthrough for non-finalized blocks.
        for i in 0..block_order.len() {
            let id = block_order[i];
            let block = blocks.get(&id).unwrap();
            if block.successors.is_empty() && !block.finalized {
                if let Some(&next_id) = block_order.get(i + 1) {
                    blocks.get_mut(&id).unwrap().successors.push(next_id);
                }
            }
        }

        // Fallthrough elimination.
        for i in 0..block_order.len() {
            let id = block_order[i];
            let next_id = block_order.get(i + 1).copied();
            let block = blocks.get(&id).unwrap();
            if let Some(LowerInst::Ir(IrInst::Branch { target })) = block.instructions.last() {
                if Some(*target) == next_id {
                    let block = blocks.get_mut(&id).unwrap();
                    let inst = block.instructions.pop().unwrap();
                    if let LowerInst::Ir(ir) = inst {
                        block
                            .instructions
                            .push(LowerInst::Ir(IrInst::Skipped(Box::new(ir))));
                    }
                }
            }
        }

        let func = IRFunction {
            config: self.config,
            regions: self.regions,
            vreg_defs,
            vreg_refs,
            block_order,
            blocks,
        };

        self.cb.push_function(func);
    }

    // --- internal helpers ---

    fn ensure_block(&mut self, id: BlockId) {
        if !self.blocks.contains_key(&id) {
            self.block_order.push(id);
            self.blocks.insert(
                id,
                IrBlock {
                    successors: Vec::new(),
                    instructions: Vec::new(),
                    finalized: false,
                    defs: HashSet::new(),
                    uses: HashSet::new(),
                    params: HashSet::new(),
                    results: HashSet::new(),
                    remaining_uses: HashMap::new(),
                },
            );
        }
    }

    fn snapshot_regions_onto(&mut self, target: BlockId) {
        self.ensure_block(target);
        let source_block = self.current_block.expect("snapshot: no active block");
        self.region_snapshots
            .entry(target)
            .or_default()
            .push((source_block, self.regions.clone()));
    }
}

/// Compute reverse postorder of the block graph.
///
/// For br_if blocks (two successors), visits block_else first so that
/// block_if (the fall-through target) is placed immediately after the
/// branch block in the final order.
fn rpo(entry: &BlockId, blocks: &HashMap<BlockId, IrBlock>) -> Vec<BlockId> {
    let mut visited = HashSet::new();
    let mut postorder = Vec::new();

    fn dfs(
        id: BlockId,
        blocks: &HashMap<BlockId, IrBlock>,
        visited: &mut HashSet<BlockId>,
        postorder: &mut Vec<BlockId>,
    ) {
        if !visited.insert(id) {
            return;
        }
        let block = &blocks[&id];
        // Visit successors in reverse so the first successor (block_if
        // for br_if, or the branch target) ends up right after this
        // block in RPO.
        for &succ in block.successors.iter().rev() {
            dfs(succ, blocks, visited, postorder);
        }
        postorder.push(id);
    }

    dfs(*entry, blocks, &mut visited, &mut postorder);
    postorder.reverse();
    postorder
}
