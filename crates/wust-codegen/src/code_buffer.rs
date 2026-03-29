use std::collections::BTreeMap;

use autosynth_emitter::CodeContext;
use autosynth_ir::Label;
use wust_core::mmap::{MmapRegion, Protection, align_up, page_size};

/// Default reservation: 128MB virtual address space.
const DEFAULT_RESERVE_PAGES: usize = 128 * 1024 * 1024 / 4096;

/// Initial committed region: 64KB.
const INITIAL_COMMIT_PAGES: usize = 16;

/// Executable memory region for JIT-compiled code.
///
/// Manages the mmap lifecycle: reserve virtual address space, commit
/// pages as RW, finalize to execute-only, reopen for more writing.
pub struct CodeBuffer {
    region: MmapRegion,
    /// Bytes currently committed (RW). Always page-aligned.
    committed: usize,
    /// Bytes written so far.
    len: usize,
    finalized: bool,
    /// Label → byte offset mapping. Persists across finalizations.
    labels: BTreeMap<Label, usize>,
}

impl CodeBuffer {
    /// Allocate a code buffer with default sizing (128 MB reserved, 64 KB committed).
    ///
    /// Reserves virtual address space with no access, then commits an
    /// initial region as read-write for code emission.
    pub fn new() -> Result<Self, anyhow::Error> {
        let page_size = page_size();
        let initial_commit = INITIAL_COMMIT_PAGES * page_size;

        let region = MmapRegion::with_protection(DEFAULT_RESERVE_PAGES, 1, Protection::NONE)?;
        region.set_protection_range(0, initial_commit, Protection::READ_WRITE)?;

        Ok(CodeBuffer {
            region,
            committed: initial_commit,
            len: 0,
            finalized: false,
            labels: BTreeMap::new(),
        })
    }

    /// Finalize the buffer as executable — set RX permissions and
    /// invalidate the instruction cache. Call after all code has
    /// been written via [`CodeContext::emit_bytes`].
    pub fn flash(&mut self) -> anyhow::Result<()> {
        self.finalize_inner(self.len)
    }

    /// Pointer to the start of executable code. Only valid after `finalize()`.
    pub fn entry(&self) -> *const u8 {
        debug_assert!(self.finalized, "must finalize before calling entry()");
        self.region.base() as *const u8
    }

    fn ensure_space(&mut self, needed: usize) {
        if needed <= self.committed {
            return;
        }

        let page_size = page_size();
        let max_commit = self.region.usable_size();

        let mut new_committed = self.committed;
        while new_committed < needed {
            new_committed = new_committed.saturating_mul(2);
        }
        new_committed = align_up(new_committed, page_size).min(max_commit);

        assert!(
            needed <= new_committed,
            "code buffer exhausted: need {needed} bytes, max {max_commit}"
        );

        self.region
            .set_protection_range(
                self.committed,
                new_committed - self.committed,
                Protection::READ_WRITE,
            )
            .expect("code buffer grow mprotect failed");

        self.committed = new_committed;
    }

    /// Current write position (bytes emitted so far).
    pub fn len(&self) -> usize {
        self.len
    }

    fn finalize_inner(&mut self, code_len: usize) -> anyhow::Result<()> {
        self.region
            .set_protection_range(0, self.committed, Protection::EXEC)?;
        unsafe { sys_icache_invalidate(self.region.base(), code_len) };
        self.finalized = true;
        Ok(())
    }
}

impl CodeContext for CodeBuffer {
    type Error = anyhow::Error;

    fn emit_bytes(&mut self, bytes: &[u8]) -> Result<(), Self::Error> {
        if self.finalized {
            self.reopen()?;
        }
        self.ensure_space(self.len + bytes.len());
        unsafe {
            std::ptr::copy_nonoverlapping(
                bytes.as_ptr(),
                self.region.base().add(self.len),
                bytes.len(),
            );
        }
        self.len += bytes.len();
        Ok(())
    }

    fn offset(&self) -> usize {
        self.len
    }

    fn mark_label(&mut self, label: Label) {
        self.labels.insert(label, self.len);
    }

    fn label_offset(&self, label: Label) -> Option<usize> {
        self.labels.get(&label).copied()
    }

    fn write_bytes(&mut self, offset: usize, bytes: &[u8]) -> Result<(), Self::Error> {
        assert!(offset + bytes.len() <= self.len, "write_bytes out of bounds");
        if self.finalized {
            self.reopen()?;
        }
        unsafe {
            std::ptr::copy_nonoverlapping(
                bytes.as_ptr(),
                self.region.base().add(offset),
                bytes.len(),
            );
        }
        Ok(())
    }
}

impl CodeBuffer {
    fn reopen(&mut self) -> anyhow::Result<()> {
        debug_assert!(self.finalized, "buffer is not finalized");
        self.region
            .set_protection_range(0, self.committed, Protection::READ_WRITE)?;
        self.finalized = false;
        Ok(())
    }
}

/// Invalidate the instruction cache for a region of memory.
unsafe fn sys_icache_invalidate(addr: *mut u8, len: usize) {
    #[cfg(target_os = "macos")]
    {
        unsafe extern "C" {
            fn sys_icache_invalidate(start: *mut libc::c_void, size: usize);
        }
        unsafe { sys_icache_invalidate(addr as *mut libc::c_void, len) };
    }

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
