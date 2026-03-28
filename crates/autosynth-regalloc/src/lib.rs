#![no_std]
//! Register allocator — the authority on all virtual registers.
//!
//! Every VReg is born through [`RegAlloc::define`] with an explicit
//! origin ([`VInit`]). The regalloc tracks definitions and state,
//! and other passes query it to resolve operands.

extern crate alloc;

use alloc::vec::Vec;
use autosynth_ir::Operand;
use autosynth_isa::Width;

pub use autosynth_ir::{SlotRef, VInit, VRegId};

/// Metadata for a defined virtual register.
#[derive(Debug, Clone)]
pub struct VRegDef {
    pub id: VRegId,
    pub width: Width,
    pub init: VInit,
}

/// Register allocator state — the authority on all VRegs.
///
/// Every VReg is born through [`define`](Self::define) with an
/// explicit [`VInit`] origin.
#[derive(Clone)]
pub struct RegAlloc {
    defs: Vec<VRegDef>,
}

impl RegAlloc {
    pub fn new() -> Self {
        Self { defs: Vec::new() }
    }

    /// Define a new VReg. Returns the allocated VRegId.
    pub fn define(&mut self, init: VInit, width: Width) -> VRegId {
        let id = VRegId(self.defs.len() as u32);
        self.defs.push(VRegDef { id, width, init });
        id
    }

    /// Look up a VReg's definition.
    pub fn def(&self, id: VRegId) -> &VRegDef {
        &self.defs[id.0 as usize]
    }

    /// Look up a VReg's init origin.
    pub fn init(&self, id: VRegId) -> &VInit {
        &self.defs[id.0 as usize].init
    }

    /// Look up a VReg's width.
    pub fn width(&self, id: VRegId) -> Width {
        self.defs[id.0 as usize].width
    }

    /// Update a VReg's init origin (e.g. after const folding).
    pub fn set_init(&mut self, id: VRegId, init: VInit) {
        self.defs[id.0 as usize].init = init;
    }

    /// Number of defined VRegs.
    pub fn len(&self) -> usize {
        self.defs.len()
    }

    /// Try to fold a VReg operand as an immediate of type `Imm`.
    /// If the operand is a VReg with Const origin and the value fits
    /// `Imm`, returns `Some(imm)`. Otherwise returns `None`.
    pub fn try_fold_imm<Imm>(&self, op: &Operand) -> Option<Imm>
    where
        Imm: TryFrom<i64>,
    {
        let Operand::VReg { id, .. } = op else { return None };
        let VInit::Const(val) = self.init(*id) else { return None };
        Imm::try_from(*val).ok()
    }

    /// Try to evaluate a const-const ALU op at compile time.
    /// Returns the result if both operands are const.
    pub fn try_const_val(&self, op: &Operand) -> Option<i64> {
        let Operand::VReg { id, .. } = op else { return None };
        let VInit::Const(val) = self.init(*id) else { return None };
        Some(*val)
    }
}
