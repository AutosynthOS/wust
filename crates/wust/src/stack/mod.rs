use std::ptr;

use crate::Val;

const DEFAULT_STACK_PAGES: usize = 16;
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
pub(crate) struct Stack {
    mmap_base: *mut u8,
    mmap_size: usize,
    base: *mut u8,
    size: usize,
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
                size: usable_size,
                sp: 0,
            })
        }
    }

    /// Current stack pointer offset from base, in bytes.
    pub(crate) fn sp(&self) -> usize {
        self.sp
    }

    /// Reset stack pointer to a given byte offset.
    pub(crate) fn set_sp(&mut self, offset: usize) {
        self.sp = offset;
    }

    // --- Push/pop: all values stored as 8-byte (u64) slots ---

    pub(crate) fn push_u64(&mut self, val: u64) {
        unsafe {
            let dst = self.base.add(self.sp) as *mut u64;
            ptr::write(dst, val);
        }
        self.sp += 8;
    }

    pub(crate) fn pop_u64(&mut self) -> u64 {
        self.sp -= 8;
        unsafe {
            let src = self.base.add(self.sp) as *const u64;
            ptr::read(src)
        }
    }

    pub(crate) fn push_i32(&mut self, val: i32) {
        self.push_u64(val as u64);
    }

    pub(crate) fn pop_i32(&mut self) -> i32 {
        self.pop_u64() as i32
    }

    pub(crate) fn push_i64(&mut self, val: i64) {
        self.push_u64(val as u64);
    }

    pub(crate) fn pop_i64(&mut self) -> i64 {
        self.pop_u64() as i64
    }

    pub(crate) fn push_f32(&mut self, val: f32) {
        self.push_u64(val.to_bits() as u64);
    }

    pub(crate) fn pop_f32(&mut self) -> f32 {
        f32::from_bits(self.pop_u64() as u32)
    }

    pub(crate) fn push_f64(&mut self, val: f64) {
        self.push_u64(val.to_bits());
    }

    pub(crate) fn pop_f64(&mut self) -> f64 {
        f64::from_bits(self.pop_u64())
    }

    // --- Random access by byte offset (for locals, result slots) ---

    pub(crate) fn read_u64_at(&self, offset: usize) -> u64 {
        unsafe {
            let src = self.base.add(offset) as *const u64;
            ptr::read(src)
        }
    }

    pub(crate) fn write_u64_at(&mut self, offset: usize, val: u64) {
        unsafe {
            let dst = self.base.add(offset) as *mut u64;
            ptr::write(dst, val);
        }
    }

    /// Push a Val onto the stack.
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn push_pop_i32() {
        let mut s = Stack::new().unwrap();
        s.push_i32(42);
        s.push_i32(-1);
        assert_eq!(s.pop_i32(), -1);
        assert_eq!(s.pop_i32(), 42);
    }

    #[test]
    fn push_pop_i64() {
        let mut s = Stack::new().unwrap();
        s.push_i64(0x1_0000_0000);
        assert_eq!(s.pop_i64(), 0x1_0000_0000);
    }

    #[test]
    fn push_pop_f32() {
        let mut s = Stack::new().unwrap();
        s.push_f32(3.14);
        assert_eq!(s.pop_f32(), 3.14);
    }

    #[test]
    fn push_pop_f64() {
        let mut s = Stack::new().unwrap();
        s.push_f64(2.718281828);
        assert_eq!(s.pop_f64(), 2.718281828);
    }

    #[test]
    fn sp_tracks_pushes_and_pops() {
        let mut s = Stack::new().unwrap();
        assert_eq!(s.sp(), 0);
        s.push_i32(1);
        assert_eq!(s.sp(), 8);
        s.push_i32(2);
        assert_eq!(s.sp(), 16);
        s.pop_i32();
        assert_eq!(s.sp(), 8);
    }

    #[test]
    fn set_sp_resets_position() {
        let mut s = Stack::new().unwrap();
        s.push_i32(10);
        s.push_i32(20);
        assert_eq!(s.sp(), 16);
        s.set_sp(8);
        assert_eq!(s.sp(), 8);
        // The value at offset 0 is still there.
        assert_eq!(s.pop_i32(), 10);
    }

    #[test]
    fn random_access_read_write() {
        let mut s = Stack::new().unwrap();
        s.push_i32(100);
        s.push_i32(200);
        // Slot 0 = 100, slot 1 = 200
        assert_eq!(s.read_u64_at(0) as i32, 100);
        assert_eq!(s.read_u64_at(8) as i32, 200);
        // Overwrite slot 0
        s.write_u64_at(0, 999);
        assert_eq!(s.read_u64_at(0), 999);
    }
}
