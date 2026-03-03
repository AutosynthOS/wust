use crate::mmap::MmapRegion;

const DEFAULT_FIBRE_PAGES: usize = 16;
const GUARD_PAGES: usize = 1;

/// Downward-growing native call stack for JIT return addresses.
///
/// Owns the backing mmap. The `ptr` field holds the current stack
/// pointer (starts at top, grows downward). `repr(C)` so the JIT
/// can load `ptr` at a known offset from the Context pointer.
///
/// Layout:
/// ```text
/// [guard]  [usable ................]  [guard]
///  NONE     READ|WRITE                 NONE
///           ^base          ^top (initial SP)
/// ```
#[repr(C)]
pub struct FibreStackPointer {
    /// Current stack pointer. Starts at `top`, grows downward.
    pub ptr: *mut u8,
    region: MmapRegion,
}

impl FibreStackPointer {
    pub fn new() -> Result<Self, anyhow::Error> {
        let region = MmapRegion::new(DEFAULT_FIBRE_PAGES, GUARD_PAGES)?;
        let top = unsafe { region.base().add(region.usable_size() & !0xF) };
        Ok(Self { ptr: top, region })
    }
}

unsafe impl Send for FibreStackPointer {}
