//! Orchestrator — drives the backend emitter with register cache decisions.
//!
//! The orchestrator walks IR blocks, manages the register cache, and
//! calls the backend for instruction selection. It owns the code buffer,
//! patch points, and all mutable compilation state.
//!
//! The backend never sees calls, branches, or returns — the orchestrator
//! handles those entirely. The backend only does instruction selection
//! for ALU, Load, and Store via the [`BackendEmitter`] trait.

mod regcache;

use std::collections::HashMap;
use std::marker::PhantomData;

use autosynth_backend::BackendEmitter;
use autosynth_ir::{AluOp, BlockId, FunctionIdx, IrInst, Operand, Register, VReg};
use autosynth_isa::{PReg, Width};
use autosynth_lower::LowerCtx;

use regcache::RegCache;

/// Canonical memory location for a virtual register.
///
/// This is where the vreg lives on the stack — the regcache treats
/// registers as a write-back cache over these locations.
#[derive(Debug, Clone, Copy)]
pub struct SpillSlot {
    /// Base register (e.g. x29 for frame pointer).
    pub base: PReg,
    /// Byte offset from the base register.
    pub offset: u32,
}

/// Metadata about a virtual register known to the orchestrator.
pub struct VRegInfo {
    /// Register width — determines ldr/str size (w-reg vs x-reg).
    pub width: Width,
    /// Where this vreg lives in memory. `None` for temps that can't be spilled
    /// (must be consumed immediately or be rematerializable).
    pub slot: Option<SpillSlot>,
    /// Known constant value, if any. Enables immediate folding and
    /// rematerialization (movz instead of ldr from memory).
    pub const_value: Option<i64>,
}

/// A patch point — a location in the code buffer that needs a target address.
#[derive(Debug)]
pub enum PatchPoint {
    /// Conditional or unconditional branch to a block.
    Branch {
        /// Offset (in words) into the code buffer.
        code_offset: usize,
        target: BlockId,
    },
    /// Function call (bl instruction).
    Call {
        /// Offset (in words) into the code buffer.
        code_offset: usize,
        func_idx: u32,
    },
}

/// The orchestrator. Generic over the backend emitter.
///
/// Walks IR, manages the register cache, emits machine code. The backend
/// is stateless — the orchestrator calls `B::emit()` for instruction
/// selection, passing itself as the [`LowerCtx`].
pub struct Orchestrator<B: BackendEmitter> {
    /// Encoded instruction words.
    code: Vec<u32>,
    /// Register cache — tracks which vregs are in which physical registers.
    cache: RegCache,
    /// Per-vreg metadata (width, known constant value).
    vreg_info: Vec<VRegInfo>,
    /// Block label → code offset (in words).
    labels: HashMap<BlockId, usize>,
    /// Locations that need target addresses patched in.
    patches: Vec<PatchPoint>,
    _backend: PhantomData<B>,
}

impl<B: BackendEmitter> Orchestrator<B> {
    /// Create a new orchestrator with the backend's register pool.
    pub fn new(vreg_info: Vec<VRegInfo>) -> Self {
        let config = B::machine_config();
        Self {
            code: Vec::with_capacity(64),
            cache: RegCache::new(&config.pool),
            vreg_info,
            labels: HashMap::new(),
            patches: Vec::new(),
            _backend: PhantomData,
        }
    }

    /// Compile a sequence of IR blocks into machine code bytes.
    pub fn compile(&mut self, blocks: &[(BlockId, Vec<IrInst>)]) -> Result<Vec<u8>, String> {
        for (block_id, insts) in blocks {
            self.labels.insert(*block_id, self.code.len());

            if *block_id != BlockId::Entry {
                self.cache.invalidate_all();
            }

            let next_block = blocks
                .iter()
                .position(|b| b.0 == *block_id)
                .and_then(|i| blocks.get(i + 1))
                .map(|b| b.0);

            for inst in insts {
                self.lower_inst(inst, next_block)?;
            }
        }

        self.resolve_patches()?;
        Ok(self.to_bytes())
    }

    /// Dispatch a single IR instruction.
    fn lower_inst(&mut self, inst: &IrInst, next_block: Option<BlockId>) -> Result<(), String> {
        match inst {
            // Backend handles instruction selection for these.
            IrInst::Alu { .. } | IrInst::Load { .. } | IrInst::Store { .. } => {
                let bytes = B::emit(self, inst.clone())?;
                self.push_bytes(&bytes);
                Ok(())
            }

            // Orchestrator handles control flow and calls directly.
            IrInst::Branch { target } => {
                if Some(*target) == next_block {
                    return Ok(()); // fallthrough, no code needed
                }
                self.emit_branch(*target)
            }
            IrInst::BrIf {
                cond: _,
                block_if: _,
                block_else,
            } => self.emit_br_if(*block_else),
            IrInst::Call {
                func_idx,
                args,
                results,
                frame_advance,
            } => self.emit_call(func_idx, args, results, *frame_advance),
            IrInst::Return { values, flush } => self.emit_return(values, *flush),
        }
    }

    fn emit_branch(&mut self, target: BlockId) -> Result<(), String> {
        todo!("emit_branch({target})")
    }

    fn emit_br_if(&mut self, block_else: BlockId) -> Result<(), String> {
        todo!("emit_br_if(else={block_else})")
    }

    fn emit_call(
        &mut self,
        func_idx: &FunctionIdx,
        args: &[VReg],
        results: &[VReg],
        frame_advance: u32,
    ) -> Result<(), String> {
        todo!("emit_call({func_idx}, {frame_advance})")
    }

    fn emit_return(&mut self, values: &[VReg], flush: bool) -> Result<(), String> {
        todo!("emit_return(flush={flush})")
    }

    /// Push raw bytes into the code buffer (must be 4-byte aligned).
    fn push_bytes(&mut self, bytes: &[u8]) {
        for chunk in bytes.chunks_exact(4) {
            let word = u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]);
            self.code.push(word);
        }
    }

    fn resolve_patches(&mut self) -> Result<(), String> {
        todo!("resolve_patches")
    }

    fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(self.code.len() * 4);
        for &word in &self.code {
            out.extend_from_slice(&word.to_le_bytes());
        }
        out
    }
}

impl<B: BackendEmitter> LowerCtx for Orchestrator<B> {
    fn const_value(&self, vreg: VReg) -> Option<i64> {
        self.vreg_info.get(vreg.0 as usize)?.const_value
    }

    fn materialize_const(&mut self, val: i64, width: Width) -> (PReg, Width) {
        todo!("materialize_const({val}, {width})")
    }

    fn resolve_vreg(&mut self, vreg: VReg) -> (PReg, Width) {
        todo!("resolve_vreg({vreg})")
    }

    fn define_vreg(&mut self, vreg: VReg) -> (PReg, Width) {
        todo!("define_vreg({vreg})")
    }
}
