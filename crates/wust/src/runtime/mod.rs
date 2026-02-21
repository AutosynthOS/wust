mod canonical_abi;
pub mod code;
pub mod component;
pub mod error;
pub(crate) mod opcode;
mod store;
mod value;
// JIT disabled — focusing on interpreter correctness first
// #[cfg(target_arch = "aarch64")]
// pub mod jit;

pub use crate::engine::Engine;
pub use code::module::{ExportKind, Module};
pub use code::program::{call, invoke};
pub use component::{
    ComponentArg, ComponentImportDef, ComponentImportKind, ComponentInstance, ComponentResultType,
    ComponentValue,
};
pub use error::ExecError;
pub use opcode::Op;
pub use store::{EXTERN_FUNC_BASE, HostFunc, SharedStore, Store};
pub use value::Value;
