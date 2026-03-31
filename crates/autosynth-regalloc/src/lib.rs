#![no_std]
//! Virtual register allocator and per-block register state.

extern crate alloc;

mod allocator;
mod machine;
mod regstate;

pub use allocator::{SharedVRegAllocator, VRegAllocator};
pub use autosynth_ir::{SlotRef, VReg, VRegSource, VRegState};
pub use machine::MachineConfig;
pub use regstate::RegState;
