#![no_std]
//! Register allocator — the authority on all virtual registers.
//!
//! Every VReg is born through [`RegAlloc::define`] with an explicit
//! origin ([`VInit`]). The regalloc tracks definitions and state,
//! and other passes query it to resolve operands.

extern crate alloc;

use alloc::vec::Vec;
use autosynth_isa::{PReg, Width};

/// Virtual register ID — a simple index into the regalloc's def table.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VRegId(pub u32);

/// How a VReg's value was produced.
#[derive(Debug, Clone, Copy)]
pub enum VInit {
    /// Compile-time constant. Rematerializable — the regalloc can
    /// recreate the value instead of spilling.
    Const(i64),
    /// Arrived in a physical register (function params, call results).
    PReg(PReg),
    /// Produced as the destination of an instruction (ALU, load, etc.).
    InstDst,
    /// Value lives in memory at a known slot. Created after clobber
    /// to start a fresh vreg lifetime.
    Mem(SlotRef),
}

/// A resolved memory location — base register + byte offset.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SlotRef {
    pub base: PReg,
    pub offset: u32,
}

/// Metadata for a defined virtual register.
#[derive(Debug, Clone, Copy)]
pub struct VRegDef {
    pub id: VRegId,
    pub width: Width,
    pub init: VInit,
}

/// Register allocator state — the authority on all VRegs.
///
/// Every VReg is born through [`define`](Self::define) with an
/// explicit [`VInit`] origin.
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

    /// Number of defined VRegs.
    pub fn len(&self) -> usize {
        self.defs.len()
    }
}
