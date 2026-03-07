//! WASM-specific JIT compilation layer built on [`autosynth_codegen`].
//!
//! This crate bridges the generic `autosynth-codegen` IR pipeline with
//! WASM module structures from `wust-core`. It compiles WASM opcodes
//! into the autosynth IR, lowers them to native machine code via
//! an architecture backend, and manages an executable code buffer for
//! JIT execution.
//!
//! - [`JitModule`] — compiles a parsed WASM module and implements
//!   the `ModuleExecutor` trait for integration with the runtime.
//! - [`CodeBuffer`] — manages an mmap'd executable memory region with
//!   RW/RX lifecycle for writing and executing JIT code.

mod code_buffer;
mod jit_module;

pub use code_buffer::CodeBuffer;
pub use jit_module::JitModule;
