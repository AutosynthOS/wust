use crate::FuncIdx;

/// Frame header size in bytes (2 slots).
/// Slot 0 (+0): func_idx (u32) | resume_point (u32)
/// Slot 1 (+8): reserved
pub const FRAME_HEADER_SIZE: usize = size_of::<WasmFrame>();

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(C)]
pub struct WasmFrame {
    func_idx: FuncIdx,
    resume_point: ResumePoint,
    /// Padding to match the JIT's 16-byte frame header ABI.
    _reserved: u64,
}

impl WasmFrame {
    pub fn from(func_idx: FuncIdx, resume_point: u32) -> Self {
        Self {
            func_idx,
            resume_point: ResumePoint(resume_point),
            _reserved: 0,
        }
    }

    #[inline(always)]
    pub fn func_idx(&self) -> FuncIdx {
        self.func_idx
    }

    /// Read the resume point from the frame header.
    #[inline(always)]
    pub fn resume_point(&self) -> ResumePoint {
        self.resume_point
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct ResumePoint(u32);
