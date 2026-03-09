//! Re-exports from `autosynth-lower`.
//!
//! All types formerly defined here have moved to `autosynth-lower`
//! to allow `BackendEmitter` and `LowerCtx` to live in the same crate.

pub use autosynth_lower::{BackendEmitter, LowerError, MachineConfig};
