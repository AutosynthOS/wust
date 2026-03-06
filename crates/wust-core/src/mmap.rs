use std::ptr;

/// Memory protection flags for mmap regions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Protection(i32);

impl Protection {
    pub const NONE: Self = Self(libc::PROT_NONE);
    pub const READ: Self = Self(libc::PROT_READ);
    pub const READ_WRITE: Self = Self(libc::PROT_READ | libc::PROT_WRITE);
    pub const EXEC: Self = Self(libc::PROT_EXEC);
    pub const READ_EXEC: Self = Self(libc::PROT_READ | libc::PROT_EXEC);

    fn as_raw(self) -> i32 {
        self.0
    }
}

/// Guard-paged mmap allocation.
///
/// Layout:
/// ```text
/// [guard PROT_NONE] [usable region] [guard PROT_NONE]
/// ```
///
/// The usable region's initial protection is configurable. Guard pages
/// on each side trigger SIGSEGV on access — zero-cost overflow/underflow
/// detection.
pub struct MmapRegion {
    mmap_base: *mut u8,
    mmap_size: usize,
    base: *mut u8,
    usable_size: usize,
}

// MmapRegion owns a raw mmap'd pointer — safe to send across threads
// since we never alias it.
unsafe impl Send for MmapRegion {}
unsafe impl Sync for MmapRegion {}

impl MmapRegion {
    /// Allocate a new mmap region with guard pages and RW protection.
    ///
    /// `usable_pages` — number of pages in the usable region.
    /// `guard_pages` — number of PROT_NONE pages on each side.
    pub fn new(usable_pages: usize, guard_pages: usize) -> Result<Self, anyhow::Error> {
        Self::with_protection(usable_pages, guard_pages, Protection::READ_WRITE)
    }

    /// Allocate a new mmap region with guard pages and custom initial protection.
    ///
    /// `usable_pages` — number of pages in the usable region.
    /// `guard_pages` — number of PROT_NONE pages on each side.
    /// `prot` — initial protection for the usable region.
    pub fn with_protection(
        usable_pages: usize,
        guard_pages: usize,
        prot: Protection,
    ) -> Result<Self, anyhow::Error> {
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

            if prot != Protection::NONE {
                let ret = libc::mprotect(
                    usable_ptr as *mut libc::c_void,
                    usable_size,
                    prot.as_raw(),
                );
                if ret != 0 {
                    libc::munmap(ptr, total_size);
                    anyhow::bail!("mprotect failed");
                }
            }

            Ok(MmapRegion {
                mmap_base: ptr as *mut u8,
                mmap_size: total_size,
                base: usable_ptr,
                usable_size,
            })
        }
    }

    /// Start of the usable region.
    #[inline(always)]
    pub fn base(&self) -> *mut u8 {
        self.base
    }

    /// Size of the usable region in bytes.
    #[inline(always)]
    pub fn usable_size(&self) -> usize {
        self.usable_size
    }

    /// Change the protection of the entire usable region.
    pub fn set_protection(&self, prot: Protection) -> Result<(), anyhow::Error> {
        self.set_protection_range(0, self.usable_size, prot)
    }

    /// Change the protection of a sub-range within the usable region.
    ///
    /// `offset` and `len` must be page-aligned and within the usable region.
    pub fn set_protection_range(
        &self,
        offset: usize,
        len: usize,
        prot: Protection,
    ) -> Result<(), anyhow::Error> {
        assert!(
            offset + len <= self.usable_size,
            "protection range out of bounds"
        );
        let ret = unsafe {
            libc::mprotect(
                self.base.add(offset) as *mut libc::c_void,
                len,
                prot.as_raw(),
            )
        };
        anyhow::ensure!(ret == 0, "mprotect failed");
        Ok(())
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

pub fn page_size() -> usize {
    unsafe { libc::sysconf(libc::_SC_PAGESIZE) as usize }
}

pub fn align_up(val: usize, align: usize) -> usize {
    (val + align - 1) & !(align - 1)
}
