use std::ptr;

use crate::Val;

const DEFAULT_STACK_PAGES: usize = 64;
const GUARD_PAGES: usize = 1;

/// Mmap'd operand stack with guard pages on both ends.
///
/// Layout (grows upward):
/// ```text
/// [guard]  [usable ................]  [guard]
///  NONE     READ|WRITE                 NONE
///           ^base                      ^base + size
/// ```
///
/// Accessing a guard page triggers SIGSEGV — zero-cost overflow
/// and underflow detection.
///
/// # Safety: guard page limitations
///
/// Guard pages only protect against **sequential** push/pop overflow
/// and underflow (SP ± 8 stepping into a guard region). They do NOT
/// protect against computed offsets like `sp - N` or `locals_sp + i * 8`:
///
/// - A usize underflow (`0 - 8`) panics in debug or wraps in release,
///   pointing far above the allocation — never hitting the lower guard.
/// - An out-of-bounds local index could read/write arbitrary memory
///   relative to `base`.
///
/// Correctness of computed offsets relies on **wasm validation**
/// (wasmparser validates by default). Validation guarantees operand
/// stack balance and local index bounds, making these cases impossible
/// for well-formed modules. If we ever accept unvalidated bytecode,
/// explicit bounds checks must be added to `read_u64_at`, `write_u64_at`,
/// and any `sp - N` arithmetic.
pub(crate) struct Stack {
    mmap_base: *mut u8,
    mmap_size: usize,
    base: *mut u8,
    /// Stack pointer offset from `base`, in bytes. Grows upward.
    sp: usize,
}

impl Stack {
    pub(crate) fn new() -> Result<Self, anyhow::Error> {
        let page_size = page_size();
        let usable_size = DEFAULT_STACK_PAGES * page_size;
        let guard_size = GUARD_PAGES * page_size;
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
            anyhow::ensure!(ptr != libc::MAP_FAILED, "stack mmap failed");

            let usable_ptr = (ptr as *mut u8).add(guard_size);
            let ret = libc::mprotect(
                usable_ptr as *mut libc::c_void,
                usable_size,
                libc::PROT_READ | libc::PROT_WRITE,
            );
            if ret != 0 {
                libc::munmap(ptr, total_size);
                anyhow::bail!("stack mprotect failed");
            }

            Ok(Stack {
                mmap_base: ptr as *mut u8,
                mmap_size: total_size,
                base: usable_ptr,
                sp: 0,
            })
        }
    }

    /// Current stack pointer offset from base, in bytes.
    #[inline(always)]
    pub(crate) fn sp(&self) -> usize {
        self.sp
    }

    /// Reset stack pointer to a given byte offset.
    #[inline(always)]
    pub(crate) fn set_sp(&mut self, offset: usize) {
        self.sp = offset;
    }

    // --- Push/pop: all values stored as 8-byte (u64) slots ---

    #[inline(always)]
    pub(crate) fn push_u64(&mut self, val: u64) {
        unsafe {
            let dst = self.base.add(self.sp) as *mut u64;
            ptr::write(dst, val);
        }
        self.sp += 8;
    }

    #[inline(always)]
    pub(crate) fn pop_u64(&mut self) -> u64 {
        self.sp -= 8;
        unsafe {
            let src = self.base.add(self.sp) as *const u64;
            ptr::read(src)
        }
    }

    #[inline(always)]
    pub(crate) fn pop_i32(&mut self) -> i32 {
        self.pop_u64() as i32
    }

    #[inline(always)]
    pub(crate) fn push_i32(&mut self, val: i32) {
        self.push_u64(val as u64);
    }

    #[inline(always)]
    pub(crate) fn push_i64(&mut self, val: i64) {
        self.push_u64(val as u64);
    }

    #[inline(always)]
    pub(crate) fn push_f32(&mut self, val: f32) {
        self.push_u64(val.to_bits() as u64);
    }

    #[inline(always)]
    pub(crate) fn push_f64(&mut self, val: f64) {
        self.push_u64(val.to_bits());
    }

    /// Base pointer of the usable stack region.
    #[inline(always)]
    pub(crate) fn base(&self) -> *mut u8 {
        self.base
    }

    // --- Random access by byte offset (for locals, result slots) ---

    #[inline(always)]
    pub(crate) fn read_u64_at(&self, offset: usize) -> u64 {
        unsafe {
            let src = self.base.add(offset) as *const u64;
            ptr::read(src)
        }
    }

    #[inline(always)]
    pub(crate) fn write_u64_at(&mut self, offset: usize, val: u64) {
        unsafe {
            let dst = self.base.add(offset) as *mut u64;
            ptr::write(dst, val);
        }
    }

    /// Returns the address ranges of the lower and upper guard pages
    /// as `(lower_start, lower_end, upper_start, upper_end)`.
    ///
    /// Used by the trap handler to check if a SIGSEGV fault address
    /// falls within a known guard page.
    pub(crate) fn guard_page_ranges(&self) -> (usize, usize, usize, usize) {
        let page_size = page_size();
        let guard_size = GUARD_PAGES * page_size;
        let usable_size = self.mmap_size - 2 * guard_size;

        let lower_start = self.mmap_base as usize;
        let lower_end = lower_start + guard_size;
        let upper_start = self.base as usize + usable_size;
        let upper_end = upper_start + guard_size;

        (lower_start, lower_end, upper_start, upper_end)
    }

    /// Push a Val onto the stack.
    #[inline(always)]
    pub(crate) fn push_val(&mut self, val: &Val) {
        match val {
            Val::I32(v) => self.push_i32(*v),
            Val::I64(v) => self.push_i64(*v),
            Val::F32(v) => self.push_f32(*v),
            Val::F64(v) => self.push_f64(*v),
            Val::V128(v) => {
                // V128 takes two u64 slots.
                self.push_u64(*v as u64);
                self.push_u64((*v >> 64) as u64);
            }
            Val::Ref(_) => self.push_u64(0),
        }
    }
}

impl Drop for Stack {
    fn drop(&mut self) {
        unsafe {
            libc::munmap(self.mmap_base as *mut libc::c_void, self.mmap_size);
        }
    }
}

fn page_size() -> usize {
    // SAFETY: sysconf(_SC_PAGESIZE) always succeeds on POSIX systems.
    unsafe { libc::sysconf(libc::_SC_PAGESIZE) as usize }
}
