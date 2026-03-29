//! A generic, cross-architecture code generation library.
//!
//! `autosynth-codegen` provides a backend-agnostic IR, a function builder with
//! virtual-stack semantics, a write-back register cache, and pluggable backend
//! trait for lowering to native machine code. It knows nothing about any
//! specific language or runtime — the caller decides call conventions, frame
//! layouts, and register roles.

/// New VCode pipeline builder.
pub mod builder;
/// Convergence selector — phi materialization before branches.
pub mod converge;
/// Old builder (preserved for reference / old tests).
// mod builder_old;
/// IR types (IrFunction, IrBlock).
pub mod ir;
/// IR function and block types (old pipeline).
// mod ir_function;
/// Lowerer (old pipeline).
// mod lowerer;
/// New VCode pipeline — compile IrFunction through a Selector.
pub mod pipeline;
pub use autosynth_ir::{
    AluOp, BlockId, CompOp, FunctionIdx, IrInst, LowerInst, RegInst, SlotRef, VInit, VReg, VRegion,
    VRegionId,
};
pub use autosynth_isa::Width;
/// Register allocator (old pipeline).
// mod regalloc;
pub use autosynth_regalloc;
pub use builder::FunctionBuilder;
// pub use builder_old::{CodeBuilder, FunctionBuilder as OldFunctionBuilder};
// pub use lowerer::compile;
