use std::ptr;

/// Guard-paged mmap allocation.
///
/// Layout:
/// ```text
/// [guard PROT_NONE] [usable PROT_READ|PROT_WRITE] [guard PROT_NONE]
/// ```
///
/// Accessing a guard page triggers SIGSEGV — zero-cost overflow/underflow
/// detection for stacks built on top of this region.
pub struct MmapRegion {
    mmap_base: *mut u8,
    mmap_size: usize,
    base: *mut u8,
    usable_size: usize,
}

impl MmapRegion {
    /// Allocate a new mmap region with guard pages.
    ///
    /// `usable_pages` — number of read/write pages in the middle.
    /// `guard_pages` — number of PROT_NONE pages on each side.
    pub fn new(usable_pages: usize, guard_pages: usize) -> Result<Self, anyhow::Error> {
        let page_size = page_size();
        let usable_size = usable_pages * page_size;
        let guard_size = guard_pages * page_size;
        let total_size = usable_size + 2 * guard_size;

        unsafe {
            let ptr = libc::mmap(
                ptr::null_mut(),
                total_size,
                libc::PROT_NONE,
                libc::MAP_PRIVATE | libc::MAP_ANON,
                -1,
                0,
            );
            anyhow::ensure!(ptr != libc::MAP_FAILED, "mmap failed");

            let usable_ptr = (ptr as *mut u8).add(guard_size);
            let ret = libc::mprotect(
                usable_ptr as *mut libc::c_void,
                usable_size,
                libc::PROT_READ | libc::PROT_WRITE,
            );
            if ret != 0 {
                libc::munmap(ptr, total_size);
                anyhow::bail!("mprotect failed");
            }

            Ok(MmapRegion {
                mmap_base: ptr as *mut u8,
                mmap_size: total_size,
                base: usable_ptr,
                usable_size,
            })
        }
    }

    /// Start of the usable (read/write) region.
    #[inline(always)]
    pub fn base(&self) -> *mut u8 {
        self.base
    }

    /// Size of the usable region in bytes.
    #[inline(always)]
    pub fn usable_size(&self) -> usize {
        self.usable_size
    }

    /// Address ranges of the lower and upper guard pages.
    ///
    /// Returns `(lower_start, lower_end, upper_start, upper_end)`.
    pub fn guard_ranges(&self) -> (usize, usize, usize, usize) {
        let lower_start = self.mmap_base as usize;
        let lower_end = self.base as usize;
        let upper_start = self.base as usize + self.usable_size;
        let upper_end = self.mmap_base as usize + self.mmap_size;
        (lower_start, lower_end, upper_start, upper_end)
    }
}

impl Drop for MmapRegion {
    fn drop(&mut self) {
        unsafe {
            libc::munmap(self.mmap_base as *mut libc::c_void, self.mmap_size);
        }
    }
}

fn page_size() -> usize {
    unsafe { libc::sysconf(libc::_SC_PAGESIZE) as usize }
}
