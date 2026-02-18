pub mod module;
mod store;
pub mod exec;
mod value;
// JIT disabled — focusing on interpreter correctness first
// #[cfg(target_arch = "aarch64")]
// pub mod jit;

pub use module::{Module, ExportKind};
pub use store::{Store, HostFunc, EXTERN_FUNC_BASE};
pub use exec::ExecError;
pub use value::Value;
