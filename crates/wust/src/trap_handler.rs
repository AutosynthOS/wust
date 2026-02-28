//! Signal-based trap recovery for wasm stack overflow.
//!
//! When wasm execution overflows the mmap'd operand stack, the write
//! hits a PROT_NONE guard page and the OS delivers SIGSEGV/SIGBUS.
//! This module installs a signal handler that catches guard-page faults
//! and uses sigsetjmp/siglongjmp to recover back to the interpreter
//! entry point, converting the crash into a `Trap::StackOverflow`.
//!
//! # Safety
//!
//! - The signal handler is async-signal-safe: it only reads thread-local
//!   data and calls siglongjmp, both permitted by POSIX.
//! - siglongjmp skips Rust destructors between sigsetjmp and the fault.
//!   The only heap allocation in that path is `block_frames: Vec<...>`
//!   in `execute()`, which is small and bounded. This leak is acceptable.
//! - Non-guard-page faults are chained to the previous handler.

use std::cell::UnsafeCell;
use std::sync::Once;

use crate::interpreter::Trap;

/// Alternate signal stack size (bytes). 64 KB is generous.
const ALT_STACK_SIZE: usize = 64 * 1024;

/// Fixed-size buffer for sigjmp_buf. 256 bytes covers all platforms
/// (macOS aarch64 needs 192, x86_64 needs ~200).
const JMP_BUF_SIZE: usize = 256;

unsafe extern "C" {
    fn sigsetjmp(buf: *mut u8, save_signals: libc::c_int) -> libc::c_int;
    fn siglongjmp(buf: *mut u8, val: libc::c_int) -> !;
}

/// Thread-local trap context for signal handler recovery.
struct TrapContext {
    /// sigsetjmp recovery buffer.
    jmp_buf: [u8; JMP_BUF_SIZE],
    /// Whether a recovery point is active.
    active: bool,
    /// Registered guard page ranges: (start_addr, end_addr).
    guard_pages: Vec<(usize, usize)>,
}

impl TrapContext {
    const fn new() -> Self {
        Self {
            jmp_buf: [0u8; JMP_BUF_SIZE],
            active: false,
            guard_pages: Vec::new(),
        }
    }
}

// UnsafeCell because the signal handler needs mutable access without
// going through RefCell (which is not async-signal-safe).
thread_local! {
    static TRAP_CTX: UnsafeCell<TrapContext> = const { UnsafeCell::new(TrapContext::new()) };
}

/// Previous SIGSEGV handler, saved for chaining.
static mut PREV_SIGSEGV: libc::sigaction = unsafe { std::mem::zeroed() };

static INSTALL_ONCE: Once = Once::new();

/// Install the global SIGSEGV/SIGBUS handler. Idempotent.
pub(crate) fn init() {
    INSTALL_ONCE.call_once(|| unsafe { install_handler() });
}

unsafe fn install_handler() {
    unsafe {
        // Allocate an alternate signal stack so the handler can run
        // even when the wasm operand stack is exhausted.
        let alt_stack = libc::mmap(
            std::ptr::null_mut(),
            ALT_STACK_SIZE,
            libc::PROT_READ | libc::PROT_WRITE,
            libc::MAP_PRIVATE | libc::MAP_ANON,
            -1,
            0,
        );
        assert_ne!(alt_stack, libc::MAP_FAILED, "alt stack mmap failed");

        let ss = libc::stack_t {
            ss_sp: alt_stack,
            ss_flags: 0,
            ss_size: ALT_STACK_SIZE,
        };
        let ret = libc::sigaltstack(&ss, std::ptr::null_mut());
        assert_eq!(ret, 0, "sigaltstack failed");

        let mut sa: libc::sigaction = std::mem::zeroed();
        sa.sa_sigaction = sigsegv_handler as *const () as usize;
        sa.sa_flags = libc::SA_SIGINFO | libc::SA_ONSTACK;
        libc::sigemptyset(&mut sa.sa_mask);

        let ret = libc::sigaction(libc::SIGSEGV, &sa, std::ptr::addr_of_mut!(PREV_SIGSEGV));
        assert_eq!(ret, 0, "sigaction SIGSEGV failed");

        // macOS delivers SIGBUS for mmap guard page faults.
        let ret = libc::sigaction(libc::SIGBUS, &sa, std::ptr::null_mut());
        assert_eq!(ret, 0, "sigaction SIGBUS failed");
    }
}

/// SIGSEGV/SIGBUS handler. Checks if the fault address is in a known
/// guard page; if so, siglongjmps back to the recovery point.
unsafe extern "C" fn sigsegv_handler(
    sig: libc::c_int,
    info: *mut libc::siginfo_t,
    ucontext: *mut libc::c_void,
) {
    let fault_addr = unsafe { (*info).si_addr as usize };

    TRAP_CTX.with(|cell| {
        let ctx = unsafe { &mut *cell.get() };
        if !ctx.active {
            unsafe { chain_to_previous(sig, info, ucontext) };
            return;
        }

        let is_guard = ctx.guard_pages.iter().any(|(start, end)| {
            fault_addr >= *start && fault_addr < *end
        });

        if is_guard {
            ctx.active = false;
            unsafe { siglongjmp(ctx.jmp_buf.as_mut_ptr(), 1) };
        } else {
            unsafe { chain_to_previous(sig, info, ucontext) };
        }
    });
}

/// Chain to the previous signal handler for non-guard-page faults.
unsafe fn chain_to_previous(
    sig: libc::c_int,
    info: *mut libc::siginfo_t,
    ucontext: *mut libc::c_void,
) {
    let prev = unsafe { std::ptr::addr_of!(PREV_SIGSEGV).read() };
    if prev.sa_flags & libc::SA_SIGINFO != 0 {
        let handler: unsafe extern "C" fn(libc::c_int, *mut libc::siginfo_t, *mut libc::c_void) =
            unsafe { std::mem::transmute(prev.sa_sigaction) };
        unsafe { handler(sig, info, ucontext) };
    } else {
        let handler = prev.sa_sigaction;
        if handler == libc::SIG_DFL {
            unsafe {
                libc::signal(sig, libc::SIG_DFL);
                libc::raise(sig);
            }
        } else if handler != libc::SIG_IGN {
            let handler: unsafe extern "C" fn(libc::c_int) =
                unsafe { std::mem::transmute(handler) };
            unsafe { handler(sig) };
        }
    }
}

/// Enter wasm execution with guard-page trap recovery.
///
/// Registers the given guard page ranges in thread-local storage, sets
/// up a sigsetjmp recovery point, and runs `f`. If a SIGSEGV/SIGBUS
/// hits a registered guard page during `f`, the signal handler
/// siglongjmps back here and we return `Err(Trap::StackOverflow)`.
pub(crate) fn enter_wasm<F>(guard_pages: (usize, usize, usize, usize), f: F) -> Result<(), Trap>
where
    F: FnOnce() -> Result<(), Trap>,
{
    let (lower_start, lower_end, upper_start, upper_end) = guard_pages;

    // Register guard pages in TLS.
    TRAP_CTX.with(|cell| {
        let ctx = unsafe { &mut *cell.get() };
        ctx.guard_pages.push((lower_start, lower_end));
        ctx.guard_pages.push((upper_start, upper_end));
    });

    // Set up recovery point.
    let recovered = TRAP_CTX.with(|cell| {
        let ctx = unsafe { &mut *cell.get() };
        let ret = unsafe { sigsetjmp(ctx.jmp_buf.as_mut_ptr(), 0) };
        if ret == 0 {
            ctx.active = true;
            false
        } else {
            true
        }
    });

    if recovered {
        deregister_guard_pages();
        return Err(Trap::StackOverflow);
    }

    let result = f();

    // Deactivate recovery and deregister guard pages.
    TRAP_CTX.with(|cell| {
        let ctx = unsafe { &mut *cell.get() };
        ctx.active = false;
    });
    deregister_guard_pages();

    result
}

/// Remove the two most recently registered guard page ranges.
fn deregister_guard_pages() {
    TRAP_CTX.with(|cell| {
        let ctx = unsafe { &mut *cell.get() };
        let new_len = ctx.guard_pages.len().saturating_sub(2);
        ctx.guard_pages.truncate(new_len);
    });
}
