use std::ptr;

use crate::mmap::MmapRegion;
use crate::task::frame::{FRAME_HEADER_SIZE, WasmFrame};

const DEFAULT_STACK_PAGES: usize = 64;
const GUARD_PAGES: usize = 1;

/// Wasm operand/local stack with guard pages.
///
/// Owns the backing mmap. The `ptr` field holds the current frame
/// pointer. `repr(C)` so the JIT can load `ptr` at a known offset
/// from the Context pointer.
///
/// Layout:
/// ```text
/// [guard]  [usable ................]  [guard]
///  NONE     READ|WRITE                 NONE
///           ^base (initial fp)
/// ```
#[repr(C)]
pub struct WasmFramePointer {
    /// Current frame pointer. Points to the active frame header.
    pub ptr: *mut u8,
    region: MmapRegion,
}

impl WasmFramePointer {
    /// Allocate a new wasm stack and write the initial frame header.
    pub fn new(frame: WasmFrame) -> Result<Self, anyhow::Error> {
        let region = MmapRegion::new(DEFAULT_STACK_PAGES, GUARD_PAGES)?;
        let base = region.base();
        unsafe {
            ptr::copy_nonoverlapping(
                &frame as *const WasmFrame as *const u8,
                base,
                size_of::<WasmFrame>(),
            );
        }
        Ok(Self { ptr: base, region })
    }

    /// Read the current frame header.
    #[inline(always)]
    pub fn frame(&self) -> &WasmFrame {
        unsafe { &*(self.ptr as *const WasmFrame) }
    }

    /// Write a u64 value at a slot offset (relative to frame header end).
    #[inline(always)]
    pub fn write_local(&self, offset: usize, val: u64) {
        unsafe {
            let dst = self.ptr.add(FRAME_HEADER_SIZE + offset) as *mut u64;
            ptr::write(dst, val);
        }
    }

    /// Read a u64 value at a slot offset (relative to frame header end).
    #[inline(always)]
    pub fn read_local(&self, offset: usize) -> u64 {
        unsafe {
            let src = self.ptr.add(FRAME_HEADER_SIZE + offset) as *const u64;
            ptr::read(src)
        }
    }

    /// Base pointer of the usable stack region.
    #[inline(always)]
    pub fn base(&self) -> *mut u8 {
        self.region.base()
    }

    /// Guard page address ranges for trap detection.
    pub fn guard_ranges(&self) -> (usize, usize, usize, usize) {
        self.region.guard_ranges()
    }
}

unsafe impl Send for WasmFramePointer {}
