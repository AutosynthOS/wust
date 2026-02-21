//! Execution stack backed by mmap'd memory with a guard page.
//!
//! All methods are safe to call — the guard page catches overflow
//! via SIGSEGV, and WASM validation guarantees balanced push/pop.
//! Raw pointer operations are encapsulated inside each method.

/// Default stack capacity: 1MB (virtual memory, demand-paged).
const DEFAULT_CAPACITY: usize = 1024 * 1024;

/// An execution stack backed by mmap'd memory with a guard page.
///
/// The API is safe — unsafety is encapsulated inside each method.
/// Overflow hits the guard page (SIGSEGV) rather than corrupting memory.
pub(crate) struct Stack {
    base: *mut u8,
    sp: u32,
    mmap_size: usize,
}

impl Stack {
    pub(crate) fn new() -> Self {
        Self::with_capacity(DEFAULT_CAPACITY)
    }

    pub(crate) fn with_capacity(capacity: usize) -> Self {
        let page_size = page_size();
        let capacity = round_up_to_page(capacity, page_size);
        let mmap_size = capacity + page_size;

        unsafe {
            let base = libc::mmap(
                std::ptr::null_mut(),
                mmap_size,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_PRIVATE | libc::MAP_ANON,
                -1,
                0,
            );
            assert!(base != libc::MAP_FAILED, "mmap failed for stack");

            let guard = libc::mprotect(
                (base as *mut u8).add(capacity) as *mut libc::c_void,
                page_size,
                libc::PROT_NONE,
            );
            assert!(guard == 0, "mprotect failed for guard page");

            Self {
                base: base as *mut u8,
                sp: 0,
                mmap_size,
            }
        }
    }

    /// Current stack pointer (byte offset from base).
    #[inline(always)]
    pub(crate) fn sp(&self) -> u32 {
        self.sp
    }

    /// Set the stack pointer to an absolute byte offset.
    #[inline(always)]
    pub(crate) fn set_sp(&mut self, sp: u32) {
        self.sp = sp;
    }

    #[inline(always)]
    pub(crate) fn push_u64(&mut self, val: u64) {
        unsafe {
            let ptr = self.base.add(self.sp as usize) as *mut u64;
            ptr.write_unaligned(val);
        }
        self.sp += 8;
    }

    #[inline(always)]
    pub(crate) fn pop_u64(&mut self) -> u64 {
        self.sp -= 8;
        unsafe {
            let ptr = self.base.add(self.sp as usize) as *const u64;
            ptr.read_unaligned()
        }
    }

    /// Read a u64 at an absolute byte offset.
    #[inline(always)]
    pub(crate) fn read_u64(&self, offset: u32) -> u64 {
        unsafe {
            let ptr = self.base.add(offset as usize) as *const u64;
            ptr.read_unaligned()
        }
    }

    /// Write a u64 at an absolute byte offset.
    #[inline(always)]
    pub(crate) fn write_u64(&mut self, offset: u32, val: u64) {
        unsafe {
            let ptr = self.base.add(offset as usize) as *mut u64;
            ptr.write_unaligned(val);
        }
    }

    /// Returns a raw pointer to the base of the stack.
    ///
    /// For future JIT integration — native code needs the base pointer
    /// to manipulate the stack directly.
    #[allow(dead_code)]
    pub(crate) fn base_ptr(&self) -> *mut u8 {
        self.base
    }
}

impl Drop for Stack {
    fn drop(&mut self) {
        unsafe {
            let result = libc::munmap(self.base as *mut libc::c_void, self.mmap_size);
            debug_assert!(result == 0, "munmap failed");
        }
    }
}

fn page_size() -> usize {
    unsafe { libc::sysconf(libc::_SC_PAGESIZE) as usize }
}

fn round_up_to_page(size: usize, page_size: usize) -> usize {
    (size + page_size - 1) & !(page_size - 1)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn push_pop_round_trips() {
        let mut stack = Stack::new();
        stack.push_u64(42);
        stack.push_u64(0xDEAD_BEEF);
        assert_eq!(stack.pop_u64(), 0xDEAD_BEEF);
        assert_eq!(stack.pop_u64(), 42);
        assert_eq!(stack.sp(), 0);
    }

    #[test]
    fn read_write_at_offset() {
        let mut stack = Stack::new();
        stack.push_u64(0);
        stack.push_u64(0);
        stack.write_u64(0, 111);
        stack.write_u64(8, 222);
        assert_eq!(stack.read_u64(0), 111);
        assert_eq!(stack.read_u64(8), 222);
    }

    #[test]
    fn small_capacity_stack() {
        let mut stack = Stack::with_capacity(4096);
        for i in 0..100u64 {
            stack.push_u64(i);
        }
        for i in (0..100u64).rev() {
            assert_eq!(stack.pop_u64(), i);
        }
    }
}
