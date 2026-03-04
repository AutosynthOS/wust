use crate::FuncIdx;

/// Frame header at the start of every call frame. `wasm_fp.ptr` points here.
///
/// Layout: `[func_idx: u32 | resume_pc: u32 | prev_fp_offset: u32]`
///
/// `resume_pc` is where THIS frame resumes execution from. Set to 0 on
/// initial entry, updated before calls and at suspend points.
///
/// `prev_fp_offset` is the byte distance back to the caller's fp.
/// Zero means outermost frame (no caller).
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct FrameHeader {
    pub func_idx: FuncIdx,
    pub resume_pc: u32,
    pub prev_fp_offset: u32,
}

pub const FRAME_HEADER_SIZE: usize = size_of::<FrameHeader>();

impl FrameHeader {
    pub fn new(func_idx: FuncIdx, resume_pc: u32, prev_fp_offset: u32) -> Self {
        Self {
            func_idx,
            resume_pc,
            prev_fp_offset,
        }
    }
}
