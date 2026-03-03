use crate::mmap::MmapRegion;

const DEFAULT_FIBRE_PAGES: usize = 16;
const GUARD_PAGES: usize = 1;

/// Downward-growing stack for JIT return addresses.
///
/// Replaces the native stack during JIT execution so that all state
/// is serializable for suspend/resume. The JIT manages push/pop via
/// generated `str/ldr [g.sp]` instructions — this type just owns
/// the backing memory.
///
/// Layout:
/// ```text
/// [guard]  [usable ................]  [guard]
///  NONE     READ|WRITE                 NONE
///           ^base          ^top (initial SP)
/// ```
///
/// Stack grows downward from `top()` toward `base()`.
pub struct FibreStack {
    region: MmapRegion,
}

impl FibreStack {
    pub fn new() -> Result<Self, anyhow::Error> {
        Ok(FibreStack {
            region: MmapRegion::new(DEFAULT_FIBRE_PAGES, GUARD_PAGES)?,
        })
    }

    /// Top of the stack — the initial SP value.
    ///
    /// Aligned to 16 bytes as required by the aarch64 ABI.
    /// Stacks grow downward, so this is where SP starts.
    #[inline(always)]
    pub fn top(&self) -> *mut u8 {
        unsafe {
            self.region
                .base()
                .add(self.region.usable_size() & !0xF)
        }
    }
}
