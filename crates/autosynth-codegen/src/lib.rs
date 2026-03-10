//! A generic, cross-architecture code generation library.
//!
//! `autosynth-codegen` provides a backend-agnostic IR, a function builder with
//! virtual-stack semantics, a write-back register cache, and pluggable backend
//! trait for lowering to native machine code. It knows nothing about any
//! specific language or runtime — the caller decides call conventions, frame
//! layouts, and register roles.

mod builder;
/// Debug trace collector for the codegen pipeline.
pub mod debugger;
/// Orchestrator — drives the backend with register cache decisions.
mod orchestrator;
/// Register cache — write-back cache over canonical wasm stack slots.
pub mod regcache;

pub use autosynth_ir::{AluOp, BlockId, CompOp, FunctionIdx, IrInst, VInit, VReg, VRegion, VRegionId};
pub use autosynth_isa::Width;
pub use builder::{CodeBuilder, FunctionBuilder};
pub use debugger::{Align, Debugger};
pub use orchestrator::Orchestrator;
pub use regcache::{PendingStore, RegCache, ResolveResult};
