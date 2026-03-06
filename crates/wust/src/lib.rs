mod engine;
// mod interpreter; // TODO: rewrite for new WasmFramePointer API
mod jit;
mod linker;
mod module;
mod parse;
mod store;
mod trap_handler;

pub use engine::Engine;
pub use jit::codegen::Codegen;
pub use jit::{JitCompiler, JitModule};
pub use linker::Linker;
pub use module::{Module, ModuleId};
pub use store::Store;
pub use wust_codegen::disasm::CodegenOutput;
pub use wust_core::Instance;
pub use wust_core::Outcome;
pub use wust_core::Task;
pub use wust_core::Val;
pub use wust_core::exec::ModuleExecutor;
