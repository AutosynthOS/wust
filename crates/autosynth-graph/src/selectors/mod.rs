mod fuse_slots;
mod fold_imm;
mod propagate_targets;
mod spill_reload;

pub use fuse_slots::FuseSlots;
pub use fold_imm::FoldImm;
pub use propagate_targets::PropagateTargets;
pub use spill_reload::SpillReload;
