//! A generic, cross-architecture code generation library.
//!
//! `autosynth-codegen` provides a backend-agnostic IR, a function builder with
//! virtual-stack semantics, a write-back register cache, and pluggable backend
//! trait for lowering to native machine code. It knows nothing about any
//! specific language or runtime — the caller decides call conventions, frame
//! layouts, and register roles.

mod builder;
/// IR function and block types.
mod ir_function;
/// Lowerer — drives the backend with register allocation decisions.
mod lowerer;
/// Register allocator — vreg location tracking and physical register pool.
mod regalloc;
pub use autosynth_ir::{
    AluOp, BlockId, CompOp, FunctionIdx, IrInst, LowerInst, RegInst, SlotRef, VReg, VInit,
    VRegion, VRegionId,
};
pub use autosynth_isa::Width;
pub use builder::{CodeBuilder, FunctionBuilder};
pub use lowerer::compile;
