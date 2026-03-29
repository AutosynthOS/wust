#![no_std]
//! Virtual register allocator and per-block register state.
//!
//! - `VRegAllocator`: global VReg factory — defines VRegs, stores metadata.
//!   Shared via `Rc<RefCell<>>` across all blocks.
//! - `VRegState`: per-VReg live state (preg, slot, dirty).
//! - `RegState`: per-block mutable state — forked at branches, carries
//!   a shared reference to the allocator.

extern crate alloc;

use alloc::collections::BTreeMap;
use alloc::rc::Rc;
use alloc::vec;
use alloc::vec::Vec;
use core::cell::RefCell;
use autosynth_ir::{CompileError, Operand, VCode};
use autosynth_isa::{PReg, Width};

pub use autosynth_ir::{SlotRef, VInit, VReg};

/// Result of trying to fold a VReg as an immediate.
pub enum VRegOr<Imm> {
    Imm(Imm),
    VReg(VReg),
}

/// Immutable metadata for a defined virtual register.
#[derive(Debug, Clone)]
pub struct VRegDef {
    pub id: VReg,
    pub width: Width,
    pub init: VInit,
    /// Target PReg constraint.
    pub target: Option<PReg>,
}

/// A canonical memory slot with dirty tracking.
#[derive(Debug, Clone, Copy)]
pub struct SlotState {
    pub slot: SlotRef,
    pub dirty: bool,
}

/// Per-block mutable live state for a VReg.
#[derive(Debug, Clone)]
pub struct VRegState {
    /// Which PReg this VReg is currently in, if any.
    pub preg: Option<PReg>,
    /// Canonical memory slot on the managed stack.
    pub slot: Option<SlotState>,
}

impl VRegState {
    pub fn new() -> Self {
        Self {
            preg: None,
            slot: None,
        }
    }
}

// --- VRegAllocator ---

/// Global VReg factory — hands out VReg IDs and stores definitions.
#[derive(Debug, Clone)]
pub struct VRegAllocator {
    defs: Vec<VRegDef>,
}

impl VRegAllocator {
    pub fn new() -> Self {
        Self { defs: Vec::new() }
    }

    pub fn define(&mut self, init: VInit, width: Width) -> VReg {
        let id = VReg(self.defs.len() as u32);
        let target = match &init {
            VInit::PReg(preg) => Some(*preg),
            _ => None,
        };
        self.defs.push(VRegDef {
            id,
            width,
            init,
            target,
        });
        id
    }

    pub fn set_target(&mut self, id: VReg, preg: PReg) {
        self.defs[id.0 as usize].target = Some(preg);
    }

    pub fn def(&self, id: VReg) -> &VRegDef {
        &self.defs[id.0 as usize]
    }

    pub fn def_mut(&mut self, id: VReg) -> &mut VRegDef {
        &mut self.defs[id.0 as usize]
    }

    pub fn init(&self, id: VReg) -> &VInit {
        &self.defs[id.0 as usize].init
    }

    pub fn width(&self, id: VReg) -> Width {
        self.defs[id.0 as usize].width
    }

    pub fn len(&self) -> usize {
        self.defs.len()
    }
}

pub type SharedVRegAllocator = Rc<RefCell<VRegAllocator>>;

// --- RegState ---

/// Per-block register state. Forked at branch points.
/// Carries a shared reference to the VRegAllocator for def lookups.
#[derive(Clone)]
pub struct RegState {
    pub alloc: SharedVRegAllocator,
    /// Per-VReg live state — only populated for VRegs active in this block.
    pub vregs: BTreeMap<VReg, VRegState>,
    /// PReg → VReg reverse mapping. None = free.
    pub bindings: Vec<Option<VReg>>,
    pub scratch_pool: Vec<PReg>,
}

impl RegState {
    pub fn new(alloc: SharedVRegAllocator) -> Self {
        let scratch_pool: Vec<PReg> = (0..16).map(PReg).collect();
        let num_regs = 32;
        Self {
            alloc,
            vregs: BTreeMap::new(),
            bindings: vec![None; num_regs],
            scratch_pool,
        }
    }

    /// Define a new VReg through the shared allocator and initialize
    /// its live state in this block.
    pub fn define(&mut self, init: VInit, width: Width) -> VReg {
        let slot = match &init {
            VInit::Mem(s) => Some(SlotState { slot: *s, dirty: false }),
            _ => None,
        };
        let bind_preg = match &init {
            VInit::PReg(preg) => Some(*preg),
            _ => None,
        };

        let vreg = self.alloc.borrow_mut().define(init, width);
        self.vregs.insert(vreg, VRegState { preg: None, slot });

        if let Some(preg) = bind_preg {
            self.bind(vreg, preg);
        }

        vreg
    }

    /// Bind a VReg to a PReg.
    pub fn bind(&mut self, vreg: VReg, preg: PReg) {
        self.bindings[preg.0 as usize] = Some(vreg);
        self.vregs.entry(vreg).or_insert_with(VRegState::new).preg = Some(preg);
    }

    /// Unbind a VReg from its PReg.
    pub fn unbind(&mut self, vreg: VReg) {
        if let Some(state) = self.vregs.get_mut(&vreg) {
            if let Some(preg) = state.preg {
                self.bindings[preg.0 as usize] = None;
            }
            state.preg = None;
        }
    }

    /// Which PReg is this VReg in, if any?
    pub fn location(&self, vreg: VReg) -> Option<PReg> {
        self.vregs.get(&vreg).and_then(|s| s.preg)
    }

    /// Which VReg occupies this PReg, if any?
    pub fn occupant(&self, preg: PReg) -> Option<VReg> {
        self.bindings[preg.0 as usize]
    }

    /// Allocate a free scratch register.
    pub fn alloc_scratch(&self) -> Option<PReg> {
        self.scratch_pool
            .iter()
            .find(|p| self.bindings[p.0 as usize].is_none())
            .copied()
    }

    /// Allocate a physical register for a VReg.
    ///
    /// For phi VRegs: reuses the PReg of the first source that already
    /// has one, and sets target on all other sources so they converge
    /// to the same register.
    pub fn alloc_preg(&mut self, vreg: VReg) -> Result<PReg, CompileError> {
        if let Some(preg) = self.location(vreg) {
            return Ok(preg);
        }

        let alloc = self.alloc.borrow();
        let target = alloc.def(vreg).target;
        if let Some(target) = target {
            drop(alloc);
            self.bind(vreg, target);
            return Ok(target);
        }

        // Phi: find an existing PReg from sources, propagate as target.
        if let VInit::Phi(sources) = alloc.init(vreg).clone() {
            drop(alloc);
            let preg = self.alloc_phi_preg(vreg, &sources)?;
            return Ok(preg);
        }

        drop(alloc);
        let preg = self.alloc_scratch().ok_or(CompileError::RegPoolExhausted)?;
        self.bind(vreg, preg);
        Ok(preg)
    }

    /// Allocate a PReg for a phi VReg. Finds the first source that
    /// already has a PReg, uses that, and sets target on all other
    /// sources so predecessor blocks will place values there.
    fn alloc_phi_preg(&mut self, phi: VReg, sources: &[VReg]) -> Result<PReg, CompileError> {
        // Find a PReg from any source that's already allocated.
        let preg = sources.iter()
            .find_map(|&src| self.location(src))
            .or_else(|| {
                // No source has a PReg yet — pick a fresh scratch.
                self.alloc_scratch()
            })
            .ok_or(CompileError::RegPoolExhausted)?;

        // Bind the phi to this PReg.
        self.bind(phi, preg);

        // Set target on all sources so predecessors converge here.
        let mut alloc = self.alloc.borrow_mut();
        for &src in sources {
            if alloc.def(src).target.is_none() {
                alloc.set_target(src, preg);
            }
        }

        Ok(preg)
    }

    /// Resolve a VReg operand to a PReg.
    pub fn resolve_operand(&mut self, op: Operand) -> Result<Operand, CompileError> {
        match op {
            Operand::VReg(vreg) => Ok(Operand::PReg(self.alloc_preg(vreg)?)),
            other => Ok(other),
        }
    }

    /// Try to fold a VReg as an immediate, or materialize it.
    pub fn imm_or_materialize<Imm>(
        &mut self,
        operand: Operand,
        output: &mut autosynth_ir::CodeCtx,
    ) -> Result<VRegOr<Imm>, CompileError>
    where
        Imm: TryFrom<i64>,
    {
        match operand {
            Operand::Const(val) => {
                let vreg = self.define(VInit::InstDst, Width::W64);
                self.materialize_const(vreg, val, output)?;
                Ok(VRegOr::VReg(vreg))
            }
            Operand::VReg(vreg) => {
                let init = self.alloc.borrow().init(vreg).clone();
                if let VInit::Const(val) = init {
                    if let Ok(imm) = Imm::try_from(val) {
                        return Ok(VRegOr::Imm(imm));
                    }
                }
                self.materialize(vreg, output)?;
                Ok(VRegOr::VReg(vreg))
            }
            _ => unimplemented!(),
        }
    }

    /// Materialize a VReg if it's a constant or in memory.
    pub fn materialize(&mut self, vreg: VReg, output: &mut autosynth_ir::CodeCtx) -> Result<(), CompileError> {
        let init = self.alloc.borrow().init(vreg).clone();
        match init {
            VInit::Const(val) => {
                self.alloc.borrow_mut().def_mut(vreg).init = VInit::InstDst;
                self.materialize_const(vreg, val, output)?;
            }
            VInit::Mem(..) => todo!("mem materialization"),
            VInit::PReg(..) => {}
            VInit::InstDst => {}
            VInit::Phi(_) => {}
        }
        Ok(())
    }

    fn materialize_const(
        &mut self,
        vreg: VReg,
        val: i64,
        output: &mut autosynth_ir::CodeCtx,
    ) -> Result<(), CompileError> {
        self.alloc.borrow_mut().def_mut(vreg).init = VInit::InstDst;
        output.push(VCode::Materialize);
        output.push_operand(Operand::Const(val));
        output.push_operand(Operand::VReg(vreg));
        Ok(())
    }
}
