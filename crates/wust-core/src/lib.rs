#![feature(explicit_tail_calls)]
#![allow(incomplete_features)]

pub mod exec;
mod instance;
mod mmap;
pub mod module;
mod task;
mod value;

pub use instance::Instance;
pub use module::body::{Block, BlockKind, ParsedBody, slot_size};
pub use module::op::{InlineOp, OpCode};
pub use module::{FuncIdx, FuncMeta, ModuleId, ParsedModule};
pub use task::{Context, FRAME_HEADER_SIZE, FibreStackPointer, Outcome, Task, WasmFramePointer};
pub use value::{Val, WasmArgs, WasmResults, WasmVal};
