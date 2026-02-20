/// Inline function frame, pushed onto the unified stack at function entry.
///
/// 12 bytes, `#[repr(C)]` for native JIT code compatibility.
/// Fields are stored in push order: func_idx first (lowest address),
/// return_sp last (highest address).
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub(crate) struct InlineFrame {
    /// Which function is executing (index into Program.func_table).
    pub func_idx: u32,
    /// Callee's current WASM bytecode PC (instruction index into body).
    pub resume_pc: u32,
    /// Stack byte offset to unwind to on return. Points to the first
    /// result slot in the pre-call area.
    pub return_sp: u32,
}

/// Size of InlineFrame in bytes (3 x u32 = 12).
pub(crate) const INLINE_FRAME_SIZE: u32 = 12;

/// Lightweight block frame for WASM block/loop/if control flow.
///
/// 8 bytes, `#[repr(C)]`. Blocks are like functions without locals
/// or a pre-call area — just control flow metadata.
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub(crate) struct BlockFrame {
    /// Branch target PC. For blocks: end_pc. For loops: loop header PC.
    pub resume_pc: u32,
    /// Stack byte offset to unwind to on br. Points to the stack
    /// height at block entry (before any block params).
    pub return_sp: u32,
}

/// Size of BlockFrame in bytes (2 x u32 = 8).
pub(crate) const BLOCK_FRAME_SIZE: u32 = 8;
