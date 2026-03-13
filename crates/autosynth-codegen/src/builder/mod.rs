//! Builder types for incrementally constructing IR functions.
//!
//! - [`FunctionBuilder`] — builds a single [`IRFunction`]
//!   by managing blocks and VReg allocation.
//! - [`CodeBuilder`] — collects finalized functions from one or more function builders.

pub(crate) mod code_builder;
mod function_builder;

pub use code_builder::CodeBuilder;
pub use function_builder::FunctionBuilder;
