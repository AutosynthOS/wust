#![no_std]
//! Virtual register allocator and per-block register state.

extern crate alloc;

mod allocator;
mod machine;
mod regstate;
mod state;

pub use allocator::{SharedVRegAllocator, VRegAllocator, VRegDef};
pub use autosynth_ir::{SlotRef, VInit, VReg, VRegSource};
pub use machine::MachineConfig;
pub use regstate::RegState;
pub use state::{MemSlot, VRegState};
