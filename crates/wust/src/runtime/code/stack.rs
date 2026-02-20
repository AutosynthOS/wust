//! Unified execution stack backed by mmap'd memory with a guard page.
//!
//! All WASM execution state lives here: operand values, locals,
//! InlineFrames, and BlockFrames. No bounds checking on push/pop —
//! the guard page catches stack overflow via SIGSEGV.
//!
//! ## Stack Frame ABI
//!
//! The stack grows upward (increasing addresses). A function call
//! lays out the following regions contiguously:
//!
//! ```text
//!   SP → [operand stack grows here...]
//!        [local_N: u32]            ← zero-initialized extra locals
//!        [local_0 / param_0: u32]  ← param values (initialized by call logic)
//!        ─── InlineFrame (12 bytes) ───
//!        [return_sp: u32]          ← stack offset to unwind to on return
//!        [resume_pc: u32]          ← callee's current WASM bytecode PC
//!        [func_idx: u32]           ← which function is executing
//!        ─── Pre-call area ────────────
//!        [caller_resume_pc: u32]   ← where caller continues after return
//!        [result_0: u32]           ← zero-initialized, callee writes on return
//!        ← return_sp points here
//! ```

use super::frame::{BlockFrame, InlineFrame};

/// Default stack capacity: 1MB.
///
/// This is virtual memory only — physical pages are demand-paged
/// by the OS, so a large capacity costs nothing until used.
const DEFAULT_CAPACITY: usize = 1024 * 1024;

/// A unified execution stack backed by mmap'd memory with a guard page.
pub(crate) struct Stack {
    /// Base pointer of the mmap'd region.
    base: *mut u8,
    /// Current stack pointer (byte offset from base).
    sp: u32,
    /// Usable capacity in bytes (excludes the guard page).
    capacity: u32,
    /// Total mmap'd size including the guard page.
    mmap_size: usize,
}

impl Stack {
    /// Allocates a new stack with the default 1MB capacity.
    ///
    /// The stack is backed by mmap'd memory with a guard page
    /// at the end. Stack overflow triggers SIGSEGV on the guard
    /// page rather than silent memory corruption.
    pub(crate) fn new() -> Self {
        Self::with_capacity(DEFAULT_CAPACITY)
    }

    /// Allocates a new stack with the given capacity in bytes.
    ///
    /// The capacity is rounded up to the nearest page boundary.
    /// An additional guard page is appended after the usable region.
    pub(crate) fn with_capacity(capacity: usize) -> Self {
        let page_size = page_size();
        let capacity = round_up_to_page(capacity, page_size);
        let mmap_size = capacity + page_size;

        // SAFETY: We allocate anonymous private memory. The pointer is
        // valid for `mmap_size` bytes. We immediately protect the last
        // page as a guard.
        unsafe {
            let base = libc::mmap(
                std::ptr::null_mut(),
                mmap_size,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_PRIVATE | libc::MAP_ANON,
                -1,
                0,
            );

            assert!(
                base != libc::MAP_FAILED,
                "mmap failed to allocate {mmap_size} bytes for stack"
            );

            // Mark the last page as PROT_NONE — accessing it triggers SIGSEGV.
            let guard_result = libc::mprotect(
                (base as *mut u8).add(capacity) as *mut libc::c_void,
                page_size,
                libc::PROT_NONE,
            );

            assert!(
                guard_result == 0,
                "mprotect failed to set guard page"
            );

            Self {
                base: base as *mut u8,
                sp: 0,
                capacity: capacity as u32,
                mmap_size,
            }
        }
    }

    /// Returns the current stack pointer (byte offset from base).
    #[inline(always)]
    pub(crate) fn sp(&self) -> u32 {
        self.sp
    }

    /// Sets the stack pointer to an absolute byte offset.
    #[inline(always)]
    pub(crate) unsafe fn set_sp(&mut self, sp: u32) {
        self.sp = sp;
    }

    /// Pushes a u32 value onto the stack (4 bytes, 1 slot).
    #[inline(always)]
    pub(crate) unsafe fn push_u32(&mut self, val: u32) {
        unsafe {
            let ptr = self.base.add(self.sp as usize) as *mut u32;
            ptr.write_unaligned(val);
        }
        self.sp += 4;
    }

    /// Pops a u32 value from the stack (4 bytes, 1 slot).
    #[inline(always)]
    pub(crate) unsafe fn pop_u32(&mut self) -> u32 {
        self.sp -= 4;
        unsafe {
            let ptr = self.base.add(self.sp as usize) as *const u32;
            ptr.read_unaligned()
        }
    }

    /// Pushes a u64 value onto the stack (8 bytes, single write).
    #[inline(always)]
    pub(crate) unsafe fn push_u64(&mut self, val: u64) {
        unsafe {
            let ptr = self.base.add(self.sp as usize) as *mut u64;
            ptr.write_unaligned(val);
        }
        self.sp += 8;
    }

    /// Pops a u64 value from the stack (8 bytes, single read).
    #[inline(always)]
    pub(crate) unsafe fn pop_u64(&mut self) -> u64 {
        self.sp -= 8;
        unsafe {
            let ptr = self.base.add(self.sp as usize) as *const u64;
            ptr.read_unaligned()
        }
    }

    /// Reads a u32 at an absolute byte offset from the stack base.
    #[inline(always)]
    pub(crate) unsafe fn read_u32(&self, offset: u32) -> u32 {
        unsafe {
            let ptr = self.base.add(offset as usize) as *const u32;
            ptr.read_unaligned()
        }
    }

    /// Writes a u32 at an absolute byte offset from the stack base.
    #[inline(always)]
    pub(crate) unsafe fn write_u32(&mut self, offset: u32, val: u32) {
        unsafe {
            let ptr = self.base.add(offset as usize) as *mut u32;
            ptr.write_unaligned(val);
        }
    }

    /// Reads a u64 at an absolute byte offset (single 8-byte read).
    #[inline(always)]
    pub(crate) unsafe fn read_u64(&self, offset: u32) -> u64 {
        unsafe {
            let ptr = self.base.add(offset as usize) as *const u64;
            ptr.read_unaligned()
        }
    }

    /// Writes a u64 at an absolute byte offset (single 8-byte write).
    #[inline(always)]
    pub(crate) unsafe fn write_u64(&mut self, offset: u32, val: u64) {
        unsafe {
            let ptr = self.base.add(offset as usize) as *mut u64;
            ptr.write_unaligned(val);
        }
    }

    /// Pushes an InlineFrame (12 bytes: func_idx, resume_pc, return_sp).
    #[inline(always)]
    pub(crate) unsafe fn push_inline_frame(&mut self, frame: &InlineFrame) {
        unsafe {
            self.push_u32(frame.func_idx);
            self.push_u32(frame.resume_pc);
            self.push_u32(frame.return_sp);
        }
    }

    /// Reads an InlineFrame at an absolute byte offset.
    #[inline(always)]
    pub(crate) unsafe fn read_inline_frame(&self, offset: u32) -> InlineFrame {
        unsafe {
            InlineFrame {
                func_idx: self.read_u32(offset),
                resume_pc: self.read_u32(offset + 4),
                return_sp: self.read_u32(offset + 8),
            }
        }
    }

    /// Writes an InlineFrame at an absolute byte offset.
    #[inline(always)]
    pub(crate) unsafe fn write_inline_frame(&mut self, offset: u32, frame: &InlineFrame) {
        unsafe {
            self.write_u32(offset, frame.func_idx);
            self.write_u32(offset + 4, frame.resume_pc);
            self.write_u32(offset + 8, frame.return_sp);
        }
    }

    /// Pushes a BlockFrame (8 bytes: resume_pc, return_sp).
    #[inline(always)]
    pub(crate) unsafe fn push_block_frame(&mut self, frame: &BlockFrame) {
        unsafe {
            self.push_u32(frame.resume_pc);
            self.push_u32(frame.return_sp);
        }
    }

    /// Reads a BlockFrame at an absolute byte offset.
    #[inline(always)]
    pub(crate) unsafe fn read_block_frame(&self, offset: u32) -> BlockFrame {
        unsafe {
            BlockFrame {
                resume_pc: self.read_u32(offset),
                return_sp: self.read_u32(offset + 4),
            }
        }
    }

    /// Pushes N zero bytes onto the stack (for zero-initializing locals/results).
    #[inline(always)]
    pub(crate) unsafe fn push_zeroes(&mut self, byte_count: u32) {
        unsafe {
            let ptr = self.base.add(self.sp as usize);
            std::ptr::write_bytes(ptr, 0, byte_count as usize);
        }
        self.sp += byte_count;
    }
}

impl Drop for Stack {
    fn drop(&mut self) {
        // SAFETY: `base` and `mmap_size` were set by a successful mmap call.
        unsafe {
            let result = libc::munmap(self.base as *mut libc::c_void, self.mmap_size);
            debug_assert!(result == 0, "munmap failed");
        }
    }
}

/// Returns the system page size.
fn page_size() -> usize {
    // SAFETY: sysconf(_SC_PAGESIZE) is always safe and returns a positive value.
    unsafe { libc::sysconf(libc::_SC_PAGESIZE) as usize }
}

/// Rounds `size` up to the nearest multiple of `page_size`.
fn round_up_to_page(size: usize, page_size: usize) -> usize {
    (size + page_size - 1) & !(page_size - 1)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn push_pop_u32_round_trips() {
        let mut stack = Stack::new();
        unsafe {
            stack.push_u32(42);
            stack.push_u32(0xDEAD_BEEF);
            assert_eq!(stack.pop_u32(), 0xDEAD_BEEF);
            assert_eq!(stack.pop_u32(), 42);
            assert_eq!(stack.sp(), 0);
        }
    }

    #[test]
    fn push_pop_u64_round_trips() {
        let mut stack = Stack::new();
        unsafe {
            let val: u64 = 0x0123_4567_89AB_CDEF;
            stack.push_u64(val);
            assert_eq!(stack.sp(), 8); // 2 slots
            assert_eq!(stack.pop_u64(), val);
            assert_eq!(stack.sp(), 0);
        }
    }

    #[test]
    fn read_write_at_offset() {
        let mut stack = Stack::new();
        unsafe {
            // Advance SP past some space
            stack.push_zeroes(16);
            // Write at specific offsets
            stack.write_u32(0, 111);
            stack.write_u32(4, 222);
            stack.write_u32(8, 333);
            stack.write_u32(12, 444);
            assert_eq!(stack.read_u32(0), 111);
            assert_eq!(stack.read_u32(4), 222);
            assert_eq!(stack.read_u32(8), 333);
            assert_eq!(stack.read_u32(12), 444);
        }
    }

    #[test]
    fn read_write_u64_at_offset() {
        let mut stack = Stack::new();
        unsafe {
            stack.push_zeroes(8);
            let val: u64 = 0xAAAA_BBBB_CCCC_DDDD;
            stack.write_u64(0, val);
            assert_eq!(stack.read_u64(0), val);
        }
    }

    #[test]
    fn push_pop_inline_frame_round_trips() {
        let mut stack = Stack::new();
        let frame = InlineFrame {
            func_idx: 7,
            resume_pc: 42,
            return_sp: 100,
        };
        unsafe {
            let offset = stack.sp();
            stack.push_inline_frame(&frame);
            assert_eq!(stack.sp(), 12); // 3 x u32
            let read_back = stack.read_inline_frame(offset);
            assert_eq!(read_back.func_idx, 7);
            assert_eq!(read_back.resume_pc, 42);
            assert_eq!(read_back.return_sp, 100);
        }
    }

    #[test]
    fn push_pop_block_frame_round_trips() {
        let mut stack = Stack::new();
        let frame = BlockFrame {
            resume_pc: 55,
            return_sp: 200,
        };
        unsafe {
            let offset = stack.sp();
            stack.push_block_frame(&frame);
            assert_eq!(stack.sp(), 8); // 2 x u32
            let read_back = stack.read_block_frame(offset);
            assert_eq!(read_back.resume_pc, 55);
            assert_eq!(read_back.return_sp, 200);
        }
    }

    #[test]
    fn push_zeroes_initializes_to_zero() {
        let mut stack = Stack::new();
        unsafe {
            // Write non-zero values first
            stack.push_u32(0xFFFF_FFFF);
            stack.push_u32(0xFFFF_FFFF);
            // Reset SP and push zeroes over them
            stack.set_sp(0);
            stack.push_zeroes(8);
            assert_eq!(stack.read_u32(0), 0);
            assert_eq!(stack.read_u32(4), 0);
        }
    }

    #[test]
    fn small_capacity_stack() {
        // Verify that a small stack (one page) works correctly
        let mut stack = Stack::with_capacity(4096);
        unsafe {
            for i in 0..100u32 {
                stack.push_u32(i);
            }
            for i in (0..100u32).rev() {
                assert_eq!(stack.pop_u32(), i);
            }
        }
    }

    #[test]
    fn interleaved_u32_u64_operations() {
        let mut stack = Stack::new();
        unsafe {
            stack.push_u32(1);
            stack.push_u64(0x0000_0002_0000_0003);
            stack.push_u32(4);
            assert_eq!(stack.pop_u32(), 4);
            assert_eq!(stack.pop_u64(), 0x0000_0002_0000_0003);
            assert_eq!(stack.pop_u32(), 1);
        }
    }
}
