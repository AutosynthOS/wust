use super::fibre_stack::FibreStackPointer;
use super::wasm_stack::WasmFramePointer;

/// Outcome of a JIT poll — did the function return normally or suspend?
#[repr(u64)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Outcome {
    Return = 0,
    Suspended = 1,
    Running = 2,
    Ready = 3,
}

/// Runtime context passed to JIT code via a pinned register (g.ctx = x20).
///
/// Layout is `#[repr(C)]` so generated code can access fields at
/// known offsets.
#[repr(C)]
pub struct Context {
    /// Set by JIT code: 0 = Return, 1 = Suspended.
    pub outcome: Outcome,
    /// Remaining fuel for execution.
    pub fuel: i64,
    /// Current wasm frame pointer. Owns the wasm stack mmap.
    pub wasm_fp: WasmFramePointer,
    /// Current fibre stack pointer. Owns the fibre stack mmap.
    pub fibre_sp: FibreStackPointer,
}
