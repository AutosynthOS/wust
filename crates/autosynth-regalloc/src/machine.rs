//! MachineConfig — describes the target machine's register file.

use alloc::vec::Vec;
use autosynth_isa::PReg;

/// Describes a target machine's register file and reserved registers.
#[derive(Debug, Clone)]
pub struct MachineConfig {
    /// Total number of physical registers.
    pub num_regs: usize,
    /// Which PRegs are reserved (not available for scratch allocation).
    reserved: Vec<bool>,
}

impl MachineConfig {
    pub fn new(num_regs: usize) -> Self {
        Self {
            num_regs,
            reserved: alloc::vec![false; num_regs],
        }
    }

    /// Reserve a PReg — it won't be allocated as scratch.
    pub fn reserve(&mut self, preg: PReg) {
        self.reserved[preg.0 as usize] = true;
    }

    /// Is this PReg reserved?
    pub fn is_reserved(&self, preg: PReg) -> bool {
        self.reserved[preg.0 as usize]
    }

    /// The unreserved PRegs available for scratch allocation.
    pub fn scratch_pool(&self) -> Vec<PReg> {
        (0..self.num_regs as u8)
            .map(PReg)
            .filter(|p| !self.is_reserved(*p))
            .collect()
    }
}
