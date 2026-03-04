use crate::FuncIdx;

/// Frame header at the start of every call frame. `wasm_fp.ptr` points here.
///
/// Layout: `[func_idx: u32 | prev_resume_pc: u32 | prev_fp_offset: u32]`
///
/// `prev_fp_offset` is the byte distance back to the caller's FrameHeader.
/// Zero means outermost frame (no caller).
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct FrameHeader {
    func_idx: FuncIdx,
    prev_resume_pc: u32,
    prev_fp_offset: u32,
}

pub const FRAME_HEADER_SIZE: usize = size_of::<FrameHeader>();

impl FrameHeader {
    pub fn new(func_idx: FuncIdx, prev_resume_pc: u32, prev_fp_offset: u32) -> Self {
        Self {
            func_idx,
            prev_resume_pc,
            prev_fp_offset,
        }
    }

    #[inline(always)]
    pub fn func_idx(&self) -> FuncIdx {
        self.func_idx
    }

    #[inline(always)]
    pub fn prev_resume_pc(&self) -> u32 {
        self.prev_resume_pc
    }

    #[inline(always)]
    pub fn prev_fp_offset(&self) -> u32 {
        self.prev_fp_offset
    }
}
