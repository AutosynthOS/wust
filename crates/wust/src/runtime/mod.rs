pub mod module;
pub mod instruction;
pub(crate) mod opcode;
mod store;
pub mod exec;
mod value;
pub mod component;
// JIT disabled — focusing on interpreter correctness first
// #[cfg(target_arch = "aarch64")]
// pub mod jit;

pub use module::{Module, ExportKind};
pub use instruction::Instruction;
pub use opcode::Op;
pub use store::{Store, HostFunc, EXTERN_FUNC_BASE};
pub use exec::ExecError;
pub use value::Value;
pub use component::{Component, ComponentInstance, ComponentResultType};
