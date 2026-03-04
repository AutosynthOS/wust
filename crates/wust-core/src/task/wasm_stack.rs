use crate::mmap::MmapRegion;
use crate::task::frame::FrameHeader;

const DEFAULT_STACK_PAGES: usize = 64;
const GUARD_PAGES: usize = 1;

/// Wasm frame pointer with backing stack allocation.
///
/// `ptr` points at the current `FrameHeader`. Locals are below it,
/// operands are above it (after FRAME_HEADER_SIZE bytes).
/// `repr(C)` so the JIT can load `ptr` at a known offset from the
/// Context pointer.
///
/// Layout:
/// ```text
/// [guard]  [usable ................]  [guard]
///  NONE     READ|WRITE                 NONE
///           ^base
/// ```
#[repr(C)]
pub struct WasmFramePointer {
    /// Points at the current `FrameHeader`.
    pub ptr: *mut u8,
    region: MmapRegion,
}

impl WasmFramePointer {
    /// Allocate a new wasm stack. Stack top starts at base.
    pub fn new() -> Result<Self, anyhow::Error> {
        let region = MmapRegion::new(DEFAULT_STACK_PAGES, GUARD_PAGES)?;
        let base = region.base();
        Ok(Self { ptr: base, region })
    }

    /// Base pointer of the usable stack region.
    #[inline(always)]
    pub fn base(&self) -> *mut u8 {
        self.region.base()
    }

    /// Read the current frame header.
    #[inline(always)]
    pub fn frame(&self) -> &FrameHeader {
        unsafe { &*(self.ptr as *const FrameHeader) }
    }

    /// Read an i32 at `byte_offset` from the current frame pointer.
    #[inline(always)]
    pub fn read_i32(&self, byte_offset: u32) -> i32 {
        unsafe { (self.ptr.add(byte_offset as usize) as *const i32).read_unaligned() }
    }

    /// Write an i32 at `byte_offset` from the current frame pointer.
    ///
    /// Takes `&self` because writes go through the raw `ptr` field.
    /// Safety is guaranteed by the mmap backing with guard pages.
    #[inline(always)]
    pub fn write_i32(&self, byte_offset: u32, val: i32) {
        unsafe { (self.ptr.add(byte_offset as usize) as *mut i32).write_unaligned(val) }
    }

    /// Read an i64 at `byte_offset` from the current frame pointer.
    #[inline(always)]
    pub fn read_i64(&self, byte_offset: u32) -> i64 {
        unsafe { (self.ptr.add(byte_offset as usize) as *const i64).read_unaligned() }
    }

    /// Write an i64 at `byte_offset` from the current frame pointer.
    #[inline(always)]
    pub fn write_i64(&self, byte_offset: u32, val: i64) {
        unsafe { (self.ptr.add(byte_offset as usize) as *mut i64).write_unaligned(val) }
    }

    /// Guard page address ranges for trap detection.
    pub fn guard_ranges(&self) -> (usize, usize, usize, usize) {
        self.region.guard_ranges()
    }
}

unsafe impl Send for WasmFramePointer {}
