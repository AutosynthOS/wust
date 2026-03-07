//! A generic, cross-architecture code generation library.
//!
//! `autosynth-codegen` provides a backend-agnostic IR, a function builder with
//! virtual-stack semantics, a write-back register cache, and pluggable backend
//! trait for lowering to native machine code. It knows nothing about any
//! specific language or runtime — the caller decides call conventions, frame
//! layouts, and register roles.
//!
//! # Crate structure
//!
//! - [`ir`] — intermediate representation types (functions, blocks, instructions, registers).
//! - [`backend`] — the [`BackendEmitter`](backend::BackendEmitter) trait and arch-specific implementations.
//! - [`FunctionBuilder`] — incremental construction of [`ir::function::IRFunction`] via virtual stacks.
//! - [`CodeBuilder`] — collects finalized functions from one or more builders.

/// Backend trait and architecture-specific lowerers.
pub mod backend;
mod builder;
/// Disassembly metadata, register renames, and tree-style rendering.
pub mod disasm;
/// Intermediate representation types: registers, instructions, blocks, and functions.
pub mod ir;
mod regalloc;

#[cfg(test)]
mod tests;

pub use builder::{CodeBuilder, FunctionBuilder, VStack};
pub use ir::{IrType, Register, VReg, VStackId, Value};
pub use ir::block::BlockId;
pub use ir::function::{FunctionIdx, IsaReg};
pub use ir::instruction::{AluOp, CmpOp, IrInst};

/// Errors that can occur during code generation.
#[derive(Debug)]
pub enum CodegenError {
    /// All physical registers are in use and eviction is not yet implemented.
    RegisterExhaustion,
    /// A branch target label was never defined.
    UnresolvedLabel(BlockId),
    /// An immediate offset exceeds the instruction encoding range.
    OffsetOutOfRange { offset: u32, max: u32 },
    /// A virtual register appeared where only physical registers are valid.
    InvalidRegister(String),
}

impl std::fmt::Display for CodegenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CodegenError::RegisterExhaustion => {
                write!(f, "register exhaustion: no free registers (eviction not yet implemented)")
            }
            CodegenError::UnresolvedLabel(id) => {
                write!(f, "unresolved label: {id:?}")
            }
            CodegenError::OffsetOutOfRange { offset, max } => {
                write!(f, "offset {offset} out of range (max {max})")
            }
            CodegenError::InvalidRegister(msg) => {
                write!(f, "invalid register: {msg}")
            }
        }
    }
}

impl std::error::Error for CodegenError {}
