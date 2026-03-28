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

pub use autosynth_ir::{SlotRef, VInit, VReg, VRegDefId, VRegRefId};

/// Result of trying to fold a VReg as an immediate.
pub enum VRegOr<Imm> {
    Imm(Imm),
    VReg(VReg),
}

/// A VReg reference — indirection for inherited block operands.
#[derive(Debug, Clone)]
pub enum VRegRefDef {
    /// Single predecessor — just an alias for the source VReg.
    Direct(VReg),
    /// Merge point — multiple predecessors provide different VRegs.
    Phi(Vec<VReg>),
}

/// Metadata for a defined virtual register.
#[derive(Debug, Clone)]
pub struct VRegDef {
    pub id: VRegDefId,
    pub width: Width,
    pub init: VInit,
    /// Target PReg constraint. If set, the regalloc must place this
    /// VReg in this specific register (e.g. CC registers for
    /// params/returns).
    pub target: Option<PReg>,
}

/// Register allocator state.
#[derive(Clone)]
pub struct RegAlloc {
    defs: Vec<VRegDef>,
    refs: Vec<VRegRefDef>,
    /// PReg → VReg binding. None = free.
    bindings: Vec<Option<VReg>>,
    /// VRegDefId → PReg mapping. None = not in a register.
    locations: Vec<Option<PReg>>,
    scratch_pool: Vec<PReg>,
}

impl RegAlloc {
    pub fn new() -> Self {
        let scratch_pool: Vec<PReg> = (0..16).map(PReg).collect();
        let num_regs = 32;
        Self {
            defs: Vec::new(),
            refs: Vec::new(),
            bindings: vec![None; num_regs],
            locations: Vec::new(),
            scratch_pool,
        }
    }

    // --- VReg definitions ---

    pub fn define(&mut self, init: VInit, width: Width) -> VRegDefId {
        let id = VRegDefId(self.defs.len() as u32);
        let target = match init {
            VInit::PReg(preg) => Some(preg),
            _ => None,
        };
        self.defs.push(VRegDef {
            id,
            width,
            init,
            target,
        });
        self.locations.push(None);

        if let VInit::PReg(preg) = init {
            self.bind(id, preg);
        }

        id
    }

    /// Allocate a new VRegRef. Returns the RefId.
    pub fn alloc_ref(&mut self, def: VRegRefDef) -> VRegRefId {
        let id = VRegRefId(self.refs.len() as u32);
        self.refs.push(def);
        id
    }

    /// Look up a ref's definition.
    pub fn ref_def(&self, id: VRegRefId) -> &VRegRefDef {
        &self.refs[id.0 as usize]
    }

    /// Set a target PReg constraint on a VReg definition.
    pub fn set_target(&mut self, id: VRegDefId, preg: PReg) {
        self.defs[id.0 as usize].target = Some(preg);
    }

    pub fn def(&self, id: VRegDefId) -> &VRegDef {
        &self.defs[id.0 as usize]
    }

    pub fn init(&self, id: VRegDefId) -> &VInit {
        &self.defs[id.0 as usize].init
    }

    pub fn width(&self, id: VRegDefId) -> Width {
        self.defs[id.0 as usize].width
    }

    pub fn len(&self) -> usize {
        self.defs.len()
    }

    // --- Bindings ---

    /// Bind a VRegDefId to a PReg.
    fn bind(&mut self, vreg: VRegDefId, preg: PReg) {
        self.bindings[preg.0 as usize] = Some(VReg::Def(vreg));
        self.locations[vreg.0 as usize] = Some(preg);
    }

    /// Unbind a VRegDefId from its PReg.
    fn unbind(&mut self, vreg: VRegDefId) {
        if let Some(preg) = self.locations[vreg.0 as usize] {
            self.bindings[preg.0 as usize] = None;
        }
        self.locations[vreg.0 as usize] = None;
    }

    /// Which PReg is this VRegDefId in, if any?
    pub fn location(&self, vreg: VRegDefId) -> Option<PReg> {
        self.locations[vreg.0 as usize]
    }

    /// Which VReg occupies this PReg, if any?
    pub fn occupant(&self, preg: PReg) -> Option<VReg> {
        self.bindings[preg.0 as usize]
    }

    /// Allocate a free scratch register. Returns None if all are occupied.
    pub fn alloc_scratch(&self) -> Option<PReg> {
        self.scratch_pool
            .iter()
            .find(|p| self.bindings[p.0 as usize].is_none())
            .copied()
    }

    /// Allocate a physical register for a VRegDefId. If the VReg has a
    /// target PReg (from VInit::PReg), use that. Otherwise pick a
    /// free scratch register.
    pub fn alloc_preg(&mut self, vreg: VRegDefId) -> Result<PReg, CompileError> {
        // Already in a register?
        if let Some(preg) = self.location(vreg) {
            return Ok(preg);
        }

        // Has a target constraint?
        if let Some(target) = self.def(vreg).target {
            // TODO: evict if occupied
            self.bind(vreg, target);
            return Ok(target);
        }

        // Pick a free scratch register.
        let preg = self.alloc_scratch().ok_or(CompileError::RegPoolExhausted)?;
        self.bind(vreg, preg);
        Ok(preg)
    }

    /// Resolve a VRegDefId to its physical register.
    /// Allocates one if the VReg doesn't have one yet.
    pub fn resolve_vreg(&mut self, vreg: VRegDefId) -> Result<PReg, CompileError> {
        self.alloc_preg(vreg)
    }

    /// Extract a VRegDefId from a VReg enum, panicking on Ref.
    fn expect_def(vreg: VReg) -> VRegDefId {
        match vreg {
            VReg::Def(id) => id,
            VReg::Ref(_) => panic!("expected VReg::Def, got VReg::Ref"),
        }
    }

    /// Resolve any operand to its final form (PReg or immediate).
    /// VRegs get allocated to PRegs. Other operands pass through.
    pub fn resolve_operand(&mut self, op: Operand) -> Result<Operand, CompileError> {
        match op {
            Operand::VReg(vreg) => {
                let id = Self::expect_def(vreg);
                Ok(Operand::PReg(self.resolve_vreg(id)?))
            }
            other => Ok(other),
        }
    }

    // --- Immediate folding + materialization ---

    pub fn imm_or_materialize_vreg<Imm>(
        &mut self,
        vreg: VRegDefId,
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
        Ok(VRegOr::VReg(VReg::Def(vreg)))
    }

    pub fn materialize(
        &mut self,
        vreg: VRegDefId,
        output: &mut CodeCtx,
    ) -> Result<(), CompileError> {
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
                Ok(VRegOr::VReg(VReg::Def(vreg)))
            }
            Operand::VReg(vreg) => {
                let id = Self::expect_def(vreg);
                self.imm_or_materialize_vreg(id, output)
            }
            _ => unimplemented!(),
        }
    }

    fn materialize_const(
        &mut self,
        vreg: VRegDefId,
        val: i64,
        output: &mut CodeCtx,
    ) -> Result<(), CompileError> {
        self.defs[vreg.0 as usize].init = VInit::InstDst;

        output.operands.push_back(Operand::Const(val));
        output.operands.push_back(Operand::VReg(VReg::Def(vreg)));
        output.vcode.push_back(VCode::Materialize);

        Ok(())
    }
}
