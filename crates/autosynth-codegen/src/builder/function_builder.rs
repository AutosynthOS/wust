use std::collections::HashMap;

use autosynth_ir::{
    Abi, AluOp, BlockId, FunctionSignature, IrInst, LowerInst, RegInst, SlotRef, VReg, VRegDef,
    VInit, VRegion, VRegionId,
};
use autosynth_isa::{PReg, Width};

use super::code_builder::CodeBuilder;
use crate::debugger::{self, Align};
use crate::ir_function::{IRFunction, IrBlock};

/// Incrementally builds an [`IRFunction`] by emitting instructions
/// into blocks and managing VReg allocation.
pub struct FunctionBuilder<'a> {
    /// The code builder that collects finalized functions.
    cb: &'a mut CodeBuilder,

    /// The function's type signature and calling convention.
    signature: FunctionSignature,

    /// Virtual region configurations.
    pub regions: Vec<VRegion>,

    /// Per-vreg metadata, indexed by VReg id. Function-global.
    vreg_defs: Vec<VRegDef>,
    /// Next vreg id for allocation.
    next_vreg: u32,

    /// Block layout order.
    block_order: Vec<BlockId>,
    /// All blocks, keyed by BlockId.
    blocks: HashMap<BlockId, IrBlock>,
    /// The currently active block.
    current_block: Option<BlockId>,
    /// Next generated block ID (for suspend stubs, cold paths, etc.).
    next_gen_id: u32,

    /// Region snapshots saved at branch points, keyed by target block.
    region_snapshots: HashMap<BlockId, Vec<VRegion>>,
}

impl<'a> FunctionBuilder<'a> {
    pub fn new(
        cb: &'a mut CodeBuilder,
        signature: FunctionSignature,
    ) -> Self {
        debugger::dbg(|dbg| {
            dbg.add_source_column("pc", Align::Right);
            dbg.add_source_column("label", Align::Left);
        });

        Self {
            cb,
            signature,
            regions: Vec::new(),
            vreg_defs: Vec::new(),
            next_vreg: 0,
            block_order: Vec::new(),
            blocks: HashMap::new(),
            current_block: None,
            next_gen_id: 0,
            region_snapshots: HashMap::new(),
        }
    }

    // --- Region operations (inlined from VirtualMachineState) ---

    /// Register a new virtual region.
    pub fn define_region(&mut self, region: VRegion) -> VRegionId {
        let id = VRegionId(self.regions.len() as u32);
        debugger::dbg(|dbg| dbg.add_source_column(region.label, Align::Left));
        self.regions.push(region);
        id
    }

    /// Push a vreg onto a region. Emits `RegInst::SetSlot`.
    pub fn push_vreg(&mut self, region: VRegionId, vreg: VReg) {
        let index = self.regions[region.0 as usize].slots.len() as u32;
        self.regions[region.0 as usize].slots.push(vreg);
        self.emit_reg(RegInst::SetSlot { vreg, slot: SlotRef { region, index } });
    }

    /// Pop the top vreg from a region. Emits `RegInst::ClearSlot`.
    pub fn pop_any(&mut self, region: VRegionId) -> VReg {
        let index = self.regions[region.0 as usize].slots.len() as u32 - 1;
        let vreg = self.regions[region.0 as usize]
            .slots
            .pop()
            .expect("pop_any: region is empty");
        self.emit_reg(RegInst::ClearSlot { vreg, slot: SlotRef { region, index } });
        vreg
    }

    /// Read a field from a region by index.
    pub fn get_field(&self, region: VRegionId, index: usize) -> VReg {
        self.regions[region.0 as usize].slots[index]
    }

    /// Write a vreg into an existing region slot. Emits `RegInst::SetSlot`.
    pub fn set_field(&mut self, region: VRegionId, index: usize, vreg: VReg) {
        self.regions[region.0 as usize].slots[index] = vreg;
        self.emit_reg(RegInst::SetSlot { vreg, slot: SlotRef { region, index: index as u32 } });
    }

    // --- VReg allocation ---

    /// Allocate a new vreg with the given width and origin.
    ///
    /// If the origin is `VInit::PReg`, automatically emits a
    /// `RegInst::Bind` so the lowerer knows about the binding.
    pub fn alloc_vreg(&mut self, width: Width, origin: VInit) -> VReg {
        let id = VReg(self.next_vreg);
        self.next_vreg += 1;
        self.vreg_defs.push(VRegDef { id, width, origin, target: None });
        if let VInit::PReg(preg) = origin {
            self.emit_reg(RegInst::Bind { vreg: id, preg });
        }
        id
    }

    /// Get the width of a vreg.
    pub fn vreg_width(&self, vreg: VReg) -> Width {
        self.vreg_defs[vreg.0 as usize].width
    }

    /// Set the target physical register for a vreg.
    pub fn set_target(&mut self, vreg: VReg, preg: PReg) {
        self.vreg_defs[vreg.0 as usize].target = Some(preg);
    }

    // --- Debug helpers ---

    pub fn begin_op(&mut self, pc: &str, label: &str) {
        debugger::dbg(|dbg| {
            dbg.set_pending("pc", pc);
            dbg.set_pending("label", label);
        });
    }

    /// Format a vreg for debug display.
    fn fmt_vreg(&self, vreg: VReg) -> String {
        let def = &self.vreg_defs[vreg.0 as usize];
        let ty = match def.width {
            Width::W32 => "i32",
            Width::W64 => "i64",
        };
        format!("{vreg}:{ty}")
    }

    /// Snapshot all region slot states into the debugger's pending columns.
    fn snapshot_debug(&self) {
        debugger::dbg(|dbg| {
            for region in &self.regions {
                let display: String = region
                    .slots
                    .iter()
                    .map(|v| self.fmt_vreg(*v))
                    .collect::<Vec<_>>()
                    .join(" ");
                dbg.set_pending(region.label, &display);
            }
        });
    }

    // --- Block lifecycle ---

    pub fn entry_block(&mut self, block: BlockId) {
        self.ensure_block(block);
        self.current_block = Some(block);
        debugger::dbg(|dbg| dbg.mark_block_start(block));
    }

    pub fn start_block(&mut self, block: BlockId) {
        self.ensure_block(block);
        if let Some(snapshot) = self.region_snapshots.remove(&block) {
            self.regions = snapshot;
        }
        self.current_block = Some(block);
        debugger::dbg(|dbg| dbg.mark_block_start(block));
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
        self.snapshot_debug();
        debugger::dbg(|dbg| {
            dbg.record_ir_emit();
            dbg.set_source("operation", &format!("{inst}"));
        });
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

    pub fn emit_return(&mut self, operands: VRegionId) {
        match self.signature.abi {
            Abi::NativeWasm => {
                let n = self.signature.results.len();
                for i in (0..n).rev() {
                    let vreg = self.pop_any(operands);
                    self.set_target(vreg, PReg(i as u8));
                }
            }
            Abi::StackWasm => {}
        }
        self.ret();
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
        self.snapshot_debug();
        debugger::dbg(|dbg| {
            dbg.record_ir_emit();
            dbg.set_source("operation", &format!("{inst}"));
        });
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
        self.snapshot_debug();
        let desc = self.fmt_reg_inst(&inst);
        debugger::dbg(|dbg| {
            dbg.record_ir_emit();
            dbg.set_source("operation", &desc);
        });
        let block = self.blocks.get_mut(&id).unwrap();
        block.instructions.push(LowerInst::Reg(inst));
    }

    fn fmt_reg_inst(&self, inst: &RegInst) -> String {
        match inst {
            RegInst::Bind { vreg, preg } => {
                format!("{} = p{}", self.fmt_vreg(*vreg), preg.0)
            }
            RegInst::SetSlot { vreg, slot } => {
                let label = self.regions[slot.region.0 as usize].label;
                format!("{}[{}] <- {}", label, slot.index, self.fmt_vreg(*vreg))
            }
            RegInst::ClearSlot { vreg, slot } => {
                let label = self.regions[slot.region.0 as usize].label;
                format!("{}[{}]:pop -> {}", label, slot.index, self.fmt_vreg(*vreg))
            }
            RegInst::Clobber => "clobber".to_string(),
            RegInst::Use { vreg } => {
                format!("use {}", self.fmt_vreg(*vreg))
            }
        }
    }

    pub fn binop(&mut self, op: AluOp, region: VRegionId) -> VReg {
        let rhs = self.pop_any(region);
        let lhs = self.pop_any(region);
        let w = self.vreg_width(lhs);
        let dst = self.alloc_vreg(w, VInit::InstDst);
        self.emit(IrInst::Alu { op, dst, lhs, rhs });
        self.push_vreg(region, dst);
        dst
    }

    /// Finalize — produce the IRFunction.
    pub fn build(self) {
        let block_order = self.block_order;
        let mut blocks = self.blocks;

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
            regions: self.regions,
            vreg_defs: self.vreg_defs,
            block_order,
            blocks,
        };

        self.cb.push_function(func);
    }

    // --- internal helpers ---

    fn ensure_block(&mut self, id: BlockId) {
        if !self.blocks.contains_key(&id) {
            self.block_order.push(id);
            self.blocks.insert(id, IrBlock {
                successors: Vec::new(),
                instructions: Vec::new(),
                finalized: false,
            });
        }
    }

    fn snapshot_regions_onto(&mut self, target: BlockId) {
        self.ensure_block(target);
        self.region_snapshots.insert(target, self.regions.clone());
    }
}
