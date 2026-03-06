use super::fibre_stack::FibreStackPointer;
use super::wasm_stack::WasmFramePointer;

/// Outcome of a poll — did the function return normally or suspend?
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Outcome {
    Return,
    Suspended,
    Running,
    Ready,
    Call,
}

/// Runtime context passed to execution engines.
///
/// Layout is `#[repr(C)]` so generated code can access fields at
/// known offsets.
#[repr(C)]
pub struct Context {
    /// Set by engine
    pub outcome: Outcome,
    /// Remaining fuel for execution.
    pub fuel: i64,
    /// Frame pointer. Points to the current frame header `[func_idx: u32 | pc: u32]`.
    /// Operands live above fp + FRAME_HEADER_SIZE. Locals live below fp.
    pub wasm_fp: WasmFramePointer,
    /// Native fiber stack pointer (for JIT use).
    pub fibre_sp: FibreStackPointer,
}
