use std::ptr;

/// Default reservation: 128MB virtual address space.
const DEFAULT_RESERVE: usize = 128 * 1024 * 1024;

/// Initial committed region: 64KB.
const INITIAL_COMMIT: usize = 64 * 1024;

/// Executable memory buffer for JIT-compiled code.
///
/// Uses a reservation model: reserves a large virtual address range
/// (128MB) via mmap with PROT_NONE (free — no physical pages), then
/// commits pages on demand as code is emitted.
///
/// Lifecycle:
/// 1. `new(size)` — reserves virtual address space, commits initial pages
/// 2. `emit_u32(word)` — appends aarch64 instructions (auto-grows committed region)
/// 3. `finalize()` — flips committed pages to read+execute, invalidates icache
/// 4. `entry()` — returns a pointer to the start of emitted code
/// 5. `reopen()` — flips back to read+write for appending more code
///
/// A guard page at the end of the reserved region catches overflows.
/// The buffer is unmapped on drop.
pub struct CodeBuffer {
    base: *mut u8,
    /// Total mmap'd size (reserved + guard page).
    reserved: usize,
    /// Bytes currently committed (RW). Always page-aligned.
    committed: usize,
    /// Bytes emitted so far.
    len: usize,
    finalized: bool,
}

// CodeBuffer holds a raw mmap'd pointer — safe to send across threads
// since we never alias it.
unsafe impl Send for CodeBuffer {}
unsafe impl Sync for CodeBuffer {}

impl CodeBuffer {
    /// Allocate a code buffer with at least `min_size` bytes initially committed.
    ///
    /// Reserves 128MB of virtual address space (costs no physical memory),
    /// then commits enough pages to hold `min_size` bytes. A guard page
    /// (PROT_NONE) sits at the end of the reserved region.
    pub fn new(min_size: usize) -> Result<Self, anyhow::Error> {
        let page_size = page_size();
        let initial_commit = align_up(min_size.max(INITIAL_COMMIT), page_size);
        let reserve = align_up(DEFAULT_RESERVE.max(initial_commit), page_size);
        let total = reserve + page_size; // + guard page

        // Reserve entire range as PROT_NONE (no physical pages).
        let base = unsafe {
            libc::mmap(
                ptr::null_mut(),
                total,
                libc::PROT_NONE,
                libc::MAP_PRIVATE | libc::MAP_ANON,
                -1,
                0,
            )
        };
        anyhow::ensure!(base != libc::MAP_FAILED, "jit code buffer mmap failed");

        // Commit the initial region as writable.
        let ret = unsafe {
            libc::mprotect(base, initial_commit, libc::PROT_READ | libc::PROT_WRITE)
        };
        if ret != 0 {
            unsafe { libc::munmap(base, total) };
            anyhow::bail!("jit code buffer mprotect (RW) failed");
        }

        Ok(CodeBuffer {
            base: base as *mut u8,
            reserved: total,
            committed: initial_commit,
            len: 0,
            finalized: false,
        })
    }

    /// Append a 32-bit instruction word.
    ///
    /// Automatically commits more pages if needed.
    pub fn emit_u32(&mut self, word: u32) {
        debug_assert!(!self.finalized, "cannot emit after finalize");
        self.ensure_capacity(4);
        unsafe {
            let dst = self.base.add(self.len) as *mut u32;
            ptr::write(dst, word);
        }
        self.len += 4;
    }

    /// Patch a previously emitted instruction at byte offset `offset`.
    pub fn patch_u32(&mut self, offset: usize, word: u32) {
        debug_assert!(!self.finalized, "cannot patch after finalize");
        debug_assert!(offset + 4 <= self.len, "patch offset out of bounds");
        unsafe {
            let dst = self.base.add(offset) as *mut u32;
            ptr::write(dst, word);
        }
    }

    /// Read a previously emitted instruction at byte offset `offset`.
    ///
    /// Only valid before `finalize()` — finalized pages are execute-only.
    pub fn read_u32(&self, offset: usize) -> u32 {
        debug_assert!(!self.finalized, "cannot read after finalize (execute-only)");
        debug_assert!(offset + 4 <= self.len, "read offset out of bounds");
        unsafe {
            let src = self.base.add(offset) as *const u32;
            ptr::read(src)
        }
    }

    /// Flip the buffer to execute-only and invalidate the instruction cache.
    ///
    /// Pages become PROT_EXEC without PROT_READ — prevents code scanning
    /// for ROP gadgets.
    pub fn finalize(&mut self) -> Result<(), anyhow::Error> {
        debug_assert!(!self.finalized, "already finalized");

        let ret = unsafe {
            libc::mprotect(
                self.base as *mut libc::c_void,
                self.committed,
                libc::PROT_EXEC,
            )
        };
        anyhow::ensure!(ret == 0, "jit code buffer mprotect (X) failed");

        unsafe {
            sys_icache_invalidate(self.base, self.len);
        }

        self.finalized = true;
        Ok(())
    }

    /// Flip a finalized buffer back to read+write for appending more code.
    pub fn reopen(&mut self) -> Result<(), anyhow::Error> {
        debug_assert!(self.finalized, "buffer is not finalized");

        let ret = unsafe {
            libc::mprotect(
                self.base as *mut libc::c_void,
                self.committed,
                libc::PROT_READ | libc::PROT_WRITE,
            )
        };
        anyhow::ensure!(ret == 0, "jit code buffer mprotect (RW reopen) failed");

        self.finalized = false;
        Ok(())
    }

    /// Pointer to the start of emitted code. Only valid after `finalize()`.
    pub fn entry(&self) -> *const u8 {
        debug_assert!(self.finalized, "must finalize before calling entry()");
        self.base as *const u8
    }

    /// Number of bytes emitted so far.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Commit more pages if `additional` bytes would exceed the committed region.
    fn ensure_capacity(&mut self, additional: usize) {
        let needed = self.len + additional;
        if needed <= self.committed {
            return;
        }

        let page_size = page_size();
        // Guard page sits at reserved - page_size.
        let max_commit = self.reserved - page_size;

        // Double committed size until it covers the need.
        let mut new_committed = self.committed;
        while new_committed < needed {
            new_committed = new_committed.saturating_mul(2);
        }
        new_committed = align_up(new_committed, page_size).min(max_commit);

        assert!(
            needed <= new_committed,
            "code buffer exhausted: need {needed} bytes, max {max_commit}"
        );

        // Commit the new pages (from old committed to new committed).
        let ret = unsafe {
            libc::mprotect(
                self.base.add(self.committed) as *mut libc::c_void,
                new_committed - self.committed,
                libc::PROT_READ | libc::PROT_WRITE,
            )
        };
        assert!(ret == 0, "jit code buffer grow mprotect failed");

        self.committed = new_committed;
    }
}

impl Drop for CodeBuffer {
    fn drop(&mut self) {
        unsafe {
            libc::munmap(self.base as *mut libc::c_void, self.reserved);
        }
    }
}

fn page_size() -> usize {
    unsafe { libc::sysconf(libc::_SC_PAGESIZE) as usize }
}

fn align_up(val: usize, align: usize) -> usize {
    (val + align - 1) & !(align - 1)
}

/// Invalidate the instruction cache for a region of memory.
/// Required on aarch64 after writing code and before executing it.
unsafe fn sys_icache_invalidate(addr: *mut u8, len: usize) {
    // On macOS, use the sys_icache_invalidate function from libSystem.
    #[cfg(target_os = "macos")]
    {
        unsafe extern "C" {
            fn sys_icache_invalidate(start: *mut libc::c_void, size: usize);
        }
        unsafe { sys_icache_invalidate(addr as *mut libc::c_void, len) };
    }

    // On Linux, use __clear_cache from GCC builtins.
    #[cfg(target_os = "linux")]
    {
        unsafe extern "C" {
            fn __clear_cache(start: *mut libc::c_void, end: *mut libc::c_void);
        }
        unsafe {
            __clear_cache(
                addr as *mut libc::c_void,
                addr.add(len) as *mut libc::c_void,
            )
        };
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn allocate_and_finalize() {
        let mut buf = CodeBuffer::new(4096).unwrap();
        assert_eq!(buf.len(), 0);

        // Emit a RET instruction (0xd65f03c0).
        buf.emit_u32(0xd65f03c0);
        assert_eq!(buf.len(), 4);

        buf.finalize().unwrap();

        // The entry pointer should be non-null.
        assert!(!buf.entry().is_null());
    }

    #[test]
    fn emit_and_read_back() {
        let mut buf = CodeBuffer::new(4096).unwrap();
        buf.emit_u32(0xAABBCCDD);
        buf.emit_u32(0x11223344);
        assert_eq!(buf.read_u32(0), 0xAABBCCDD);
        assert_eq!(buf.read_u32(4), 0x11223344);
    }

    #[test]
    fn patch_instruction() {
        let mut buf = CodeBuffer::new(4096).unwrap();
        buf.emit_u32(0x00000000); // placeholder
        buf.emit_u32(0x11111111);
        buf.patch_u32(0, 0xFFFFFFFF);
        assert_eq!(buf.read_u32(0), 0xFFFFFFFF);
        assert_eq!(buf.read_u32(4), 0x11111111);
    }

    #[test]
    fn execute_ret_instruction() {
        let mut buf = CodeBuffer::new(4096).unwrap();

        // Emit: mov w0, #42; ret
        // MOVZ W0, #42 = 0x52800540
        // RET           = 0xd65f03c0
        buf.emit_u32(0x5280_0540);
        buf.emit_u32(0xd65f_03c0);
        buf.finalize().unwrap();

        // Call the emitted code as a function that returns i32.
        let func: unsafe extern "C" fn() -> i32 = unsafe { std::mem::transmute(buf.entry()) };
        let result = unsafe { func() };
        assert_eq!(result, 42);
    }

    #[test]
    fn reopen_and_append() {
        let mut buf = CodeBuffer::new(4096).unwrap();

        // Emit first instruction and finalize.
        buf.emit_u32(0x5280_0540); // mov w0, #42
        buf.emit_u32(0xd65f_03c0); // ret
        buf.finalize().unwrap();

        // Reopen, overwrite with new code.
        buf.reopen().unwrap();
        buf.patch_u32(0, 0x5280_0580); // mov w0, #44
        buf.finalize().unwrap();

        let func: unsafe extern "C" fn() -> i32 = unsafe { std::mem::transmute(buf.entry()) };
        let result = unsafe { func() };
        assert_eq!(result, 44);
    }
}
