pub mod module;
pub(crate) mod opcode;
mod store;
pub mod exec;
mod frame;
mod value;
pub mod component;
mod canonical_abi;
// JIT disabled — focusing on interpreter correctness first
// #[cfg(target_arch = "aarch64")]
// pub mod jit;

pub use module::{Module, ExportKind};
pub use opcode::Op;
pub use store::{Store, SharedStore, HostFunc, EXTERN_FUNC_BASE};
pub use exec::ExecError;
pub use value::Value;
pub use component::{ComponentArg, ComponentImportDef, ComponentImportKind, ComponentInstance, ComponentResultType, ComponentValue};
pub use crate::engine::Engine;
