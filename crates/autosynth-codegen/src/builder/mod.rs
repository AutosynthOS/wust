//! Builder types for incrementally constructing IR functions.
//!
//! - [`FunctionBuilder`] — builds a single [`IRFunction`](crate::ir::function::IRFunction)
//!   by managing virtual stacks, blocks, and VReg allocation.
//! - [`CodeBuilder`] — collects finalized functions from one or more function builders.

mod block_builder;
pub(crate) mod code_builder;
mod function_builder;

pub use code_builder::CodeBuilder;
pub use function_builder::FunctionBuilder;
