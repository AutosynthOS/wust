pub mod module;
mod store;
pub mod exec;
mod value;
// JIT disabled — focusing on interpreter correctness first
// #[cfg(target_arch = "aarch64")]
// pub mod jit;

pub use module::Module;
pub use store::{Store, HostFunc};
pub use exec::ExecError;
pub use value::Value;
