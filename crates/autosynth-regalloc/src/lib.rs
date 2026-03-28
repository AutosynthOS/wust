#![no_std]
//! Register allocator — the authority on all virtual registers.
//!
//! Every VReg is born through [`RegAlloc::define`] with an explicit
//! origin ([`VInit`]). The regalloc tracks definitions and state,
//! and other passes query it to resolve operands.

extern crate alloc;

use alloc::vec::Vec;
use autosynth_ir::{CodeCtx, Operand, VCode};
use autosynth_isa::Width;

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

/// Register allocator state — the authority on all VRegs.
#[derive(Clone)]
pub struct RegAlloc {
    defs: Vec<VRegDef>,
}

impl RegAlloc {
    pub fn new() -> Self {
        Self { defs: Vec::new() }
    }

    pub fn define(&mut self, init: VInit, width: Width) -> VRegId {
        let id = VRegId(self.defs.len() as u32);
        self.defs.push(VRegDef { id, width, init });
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

    pub fn set_init(&mut self, id: VRegId, init: VInit) {
        self.defs[id.0 as usize].init = init;
    }

    pub fn len(&self) -> usize {
        self.defs.len()
    }

    /// Try to fold a VReg operand as an immediate of type `Imm`.
    ///
    /// - Fits `Imm` → returns `VRegOr::Imm(imm)`.
    /// - Doesn't fit → emits `VCode::Materialize` into `output`,
    ///   updates the VReg to InstDst, returns `VRegOr::VReg(id)`.
    /// - Not a const VReg → returns `VRegOr::VReg(id)`.
    pub fn try_fold_imm<Imm>(
        &mut self,
        op: &Operand,
        output: &mut CodeCtx,
    ) -> VRegOr<Imm>
    where
        Imm: TryFrom<i64>,
    {
        let Operand::VReg(id) = op else {
            return VRegOr::VReg(VRegId(0));
        };
        let VInit::Const(val) = self.init(*id) else {
            return VRegOr::VReg(*id);
        };
        let val = *val;

        match Imm::try_from(val) {
            Ok(imm) => VRegOr::Imm(imm),
            Err(_) => {
                output.push_operand(Operand::Const(val));
                output.push_operand(*op);
                output.push_inst(VCode::Materialize);
                self.set_init(*id, VInit::InstDst);
                VRegOr::VReg(*id)
            }
        }
    }
}
