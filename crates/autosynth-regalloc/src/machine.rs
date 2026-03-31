//! MachineConfig — describes the target machine's register file.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use autosynth_isa::{IsaReg, PReg};

/// Describes a target machine's register file and reserved registers.
#[derive(Debug, Clone)]
pub struct MachineConfig {
    pub num_regs: usize,
    reserved: Vec<bool>,
    isa_regs: BTreeMap<IsaReg, PReg>,
}

impl MachineConfig {
    pub fn new(num_regs: usize, isa_regs: BTreeMap<IsaReg, PReg>) -> Self {
        let mut reserved = alloc::vec![false; num_regs];
        // Auto-reserve all ISA-mapped registers.
        for &preg in isa_regs.values() {
            reserved[preg.0 as usize] = true;
        }
        Self {
            num_regs,
            reserved,
            isa_regs,
        }
    }

    /// Reserve an additional PReg by ISA role. Returns the PReg.
    /// For FromEnd/FromStart, picks from the unreserved pool.
    pub fn reserve(&mut self, role: IsaReg) -> PReg {
        match role {
            IsaReg::FromEnd => {
                let preg = (0..self.num_regs as u8)
                    .rev()
                    .map(PReg)
                    .find(|p| !self.reserved[p.0 as usize])
                    .expect("no registers left");
                self.reserved[preg.0 as usize] = true;
                preg
            }
            IsaReg::FromStart => {
                let preg = (0..self.num_regs as u8)
                    .map(PReg)
                    .find(|p| !self.reserved[p.0 as usize])
                    .expect("no registers left");
                self.reserved[preg.0 as usize] = true;
                preg
            }
            role => {
                let preg = *self
                    .isa_regs
                    .get(&role)
                    .unwrap_or_else(|| panic!("no ISA register mapping for {role:?}"));
                self.reserved[preg.0 as usize] = true;
                preg
            }
        }
    }

    /// Look up the PReg for an ISA role.
    pub fn isa_reg(&self, role: IsaReg) -> Option<PReg> {
        self.isa_regs.get(&role).copied()
    }

    /// Expect a PReg for an ISA role
    pub fn expect_isa_reg(&self, role: IsaReg) -> PReg {
        self.isa_reg(role).expect("expected ISA Reg")
    }

    pub fn is_reserved(&self, preg: PReg) -> bool {
        self.reserved[preg.0 as usize]
    }

    pub fn scratch_pool(&self) -> Vec<PReg> {
        (0..self.num_regs as u8)
            .map(PReg)
            .filter(|p| !self.is_reserved(*p))
            .collect()
    }
}
