#![no_std]
//! Register allocator — the authority on all virtual registers.
//!
//! Every VReg is born through [`RegAlloc::define`] with an explicit
//! origin ([`VInit`]). The regalloc tracks definitions, physical
//! register bindings, and liveness state.

extern crate alloc;

use alloc::vec;
use alloc::vec::Vec;
use autosynth_ir::{CodeCtx, CompileError, Operand, VCode};
use autosynth_isa::{PReg, Width};

pub use autosynth_ir::{SlotRef, VInit, VRegId};

/// Result of trying to fold a VReg as an immediate.
pub enum VRegOr<Imm> {
    Imm(Imm),
    VReg(VRegId),
}

/// Metadata for a defined virtual register.
#[derive(Debug, Clone)]
pub struct VRegDef {
    pub id: VRegId,
    pub width: Width,
    pub init: VInit,
}

/// Register allocator state.
#[derive(Clone)]
pub struct RegAlloc {
    /// VReg definitions, indexed by VRegId.
    defs: Vec<VRegDef>,
    /// PReg → VRegId binding. None = free.
    bindings: Vec<Option<VRegId>>,
    /// VRegId → PReg mapping. None = not in a register.
    locations: Vec<Option<PReg>>,
    /// Scratch register pool (available for allocation).
    scratch_pool: Vec<PReg>,
}

impl RegAlloc {
    pub fn new() -> Self {
        // Default: x0-x15 as scratch (skip x16-x18 platform, x29 fp, x30 lr, x31 sp)
        let scratch_pool: Vec<PReg> = (0..16).map(PReg).collect();
        let num_regs = 32;
        Self {
            defs: Vec::new(),
            bindings: vec![None; num_regs],
            locations: Vec::new(),
            scratch_pool,
        }
    }

    // --- VReg definitions ---

    pub fn define(&mut self, init: VInit, width: Width) -> VRegId {
        let id = VRegId(self.defs.len() as u32);
        self.defs.push(VRegDef { id, width, init });
        self.locations.push(None);

        // If the VReg starts in a PReg, bind it immediately.
        if let VInit::PReg(preg) = init {
            self.bind(id, preg);
        }

        id
    }

    pub fn def(&self, id: VRegId) -> &VRegDef {
        &self.defs[id.0 as usize]
    }

    pub fn init(&self, id: VRegId) -> &VInit {
        &self.defs[id.0 as usize].init
    }

    pub fn width(&self, id: VRegId) -> Width {
        self.defs[id.0 as usize].width
    }

    pub fn len(&self) -> usize {
        self.defs.len()
    }

    // --- Bindings ---

    /// Bind a VReg to a PReg.
    fn bind(&mut self, vreg: VRegId, preg: PReg) {
        self.bindings[preg.0 as usize] = Some(vreg);
        self.locations[vreg.0 as usize] = Some(preg);
    }

    /// Unbind a VReg from its PReg.
    fn unbind(&mut self, vreg: VRegId) {
        if let Some(preg) = self.locations[vreg.0 as usize] {
            self.bindings[preg.0 as usize] = None;
        }
        self.locations[vreg.0 as usize] = None;
    }

    /// Which PReg is this VReg in, if any?
    pub fn location(&self, vreg: VRegId) -> Option<PReg> {
        self.locations[vreg.0 as usize]
    }

    /// Which VReg occupies this PReg, if any?
    pub fn occupant(&self, preg: PReg) -> Option<VRegId> {
        self.bindings[preg.0 as usize]
    }

    /// Allocate a free scratch register. Returns None if all are occupied.
    pub fn alloc_scratch(&self) -> Option<PReg> {
        self.scratch_pool
            .iter()
            .find(|p| self.bindings[p.0 as usize].is_none())
            .copied()
    }

    /// Allocate a register for a VReg. If the VReg has a target PReg
    /// (from VInit::PReg), use that. Otherwise pick a free scratch.
    pub fn alloc(&mut self, vreg: VRegId) -> Result<PReg, CompileError> {
        // Already in a register?
        if let Some(preg) = self.location(vreg) {
            return Ok(preg);
        }

        // Has a target constraint?
        if let VInit::PReg(target) = self.def(vreg).init {
            // TODO: evict if occupied
            self.bind(vreg, target);
            return Ok(target);
        }

        // Pick a free scratch register.
        let preg = self.alloc_scratch().ok_or(CompileError::OperandUnderflow)?; // TODO: proper error
        self.bind(vreg, preg);
        Ok(preg)
    }

    /// Resolve a VReg operand to a PReg operand.
    /// Allocates a register if the VReg doesn't have one yet.
    pub fn resolve_vreg(&mut self, vreg: VRegId) -> Result<PReg, CompileError> {
        self.alloc(vreg)
    }

    /// Resolve any operand to its final form (PReg or immediate).
    /// VRegs get allocated to PRegs. Other operands pass through.
    pub fn resolve_operand(&mut self, op: Operand) -> Result<Operand, CompileError> {
        match op {
            Operand::VReg(id) => Ok(Operand::PReg(self.resolve_vreg(id)?)),
            other => Ok(other),
        }
    }

    // --- Immediate folding + materialization ---

    pub fn imm_or_materialize_vreg<Imm>(
        &mut self,
        vreg: VRegId,
        output: &mut CodeCtx,
    ) -> Result<VRegOr<Imm>, CompileError>
    where
        Imm: TryFrom<i64>,
    {
        if let VInit::Const(val) = self.def(vreg).init {
            if let Ok(imm) = Imm::try_from(val) {
                return Ok(VRegOr::Imm(imm));
            }
        }

        self.materialize(vreg, output)?;
        Ok(VRegOr::VReg(vreg))
    }

    pub fn materialize(&mut self, vreg: VRegId, output: &mut CodeCtx) -> Result<(), CompileError> {
        match self.def(vreg).init {
            VInit::Const(val) => {
                self.defs[vreg.0 as usize].init = VInit::InstDst;
                self.materialize_const(vreg, val, output)?;
            }
            VInit::Mem(..) => todo!("mem materialization"),
            VInit::PReg(..) => {
                // TODO: emit move if target is different from current PReg
                // Already in a register, nothing to materialize.
            }
            VInit::InstDst => {}
        }
        Ok(())
    }

    pub fn imm_or_materialize<Imm>(
        &mut self,
        operand: Operand,
        output: &mut CodeCtx,
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
            Operand::VReg(vreg) => self.imm_or_materialize_vreg(vreg, output),
            _ => unimplemented!(),
        }
    }

    fn materialize_const(
        &mut self,
        vreg: VRegId,
        val: i64,
        output: &mut CodeCtx,
    ) -> Result<(), CompileError> {
        self.defs[vreg.0 as usize].init = VInit::InstDst;

        output.operands.push_back(Operand::Const(val));
        output.operands.push_back(Operand::VReg(vreg));
        output.vcode.push_back(VCode::Materialize);

        Ok(())
    }
}
