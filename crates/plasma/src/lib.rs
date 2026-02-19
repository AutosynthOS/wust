#![no_std]
extern crate alloc;

/// Dummy getrandom backend for `wasm32-unknown-unknown`.
///
/// Boa's dependency chain pulls in `getrandom`, but we don't need
/// cryptographic randomness in the embedded JS runtime. This fills
/// the buffer with zeros, which is sufficient for non-security uses.
///
/// Activated by building with `--cfg getrandom_backend="custom"`.
#[unsafe(no_mangle)]
unsafe extern "Rust" fn __getrandom_v03_custom(
    dest: *mut u8,
    len: usize,
) -> Result<(), getrandom::Error> {
    unsafe { core::ptr::write_bytes(dest, 0, len) };
    Ok(())
}

mod modules;
mod polyfills;

use alloc::alloc::Layout;
use alloc::string::ToString;
use boa_engine::native_function::NativeFunction;
use boa_engine::{Context, JsArgs, JsValue, Source, js_string};
use core::slice;
use core::str;

unsafe extern "C" {
    /// Host-provided logging function.
    /// The host reads `len` bytes of UTF-8 starting at `ptr`.
    fn host_log(ptr: *const u8, len: usize);
}

/// Allocates `size` bytes and returns a pointer to the start.
///
/// The host calls this to reserve space in linear memory before
/// writing a JS source string for `eval` to read.
#[unsafe(no_mangle)]
pub extern "C" fn alloc(size: usize) -> *mut u8 {
    let layout = Layout::from_size_align(size, 1).expect("invalid layout");
    unsafe { alloc::alloc::alloc(layout) }
}

/// Evaluates a UTF-8 JS source string located at `ptr` with length `len`.
///
/// Returns `0` on success, `1` on error.
#[unsafe(no_mangle)]
pub extern "C" fn eval(ptr: *const u8, len: usize) -> i32 {
    let source = unsafe { slice::from_raw_parts(ptr, len) };
    let source = match str::from_utf8(source) {
        Ok(s) => s,
        Err(_) => return 1,
    };

    let mut context = Context::default();
    register_console(&mut context);
    modules::register_modules(&mut context);

    match context.eval(Source::from_bytes(source)) {
        Ok(_) => 0,
        Err(e) => {
            log_error(&e);
            1
        }
    }
}

/// Logs a JS error to the host via `host_log`.
fn log_error(e: &boa_engine::JsError) {
    let msg = e.to_string();
    unsafe {
        host_log(msg.as_ptr(), msg.len());
    }
}

/// Registers a minimal `console.log` that forwards output to `host_log`.
fn register_console(context: &mut Context) {
    let log_fn = NativeFunction::from_fn_ptr(|_this, args, ctx| {
        let message = args
            .get_or_undefined(0)
            .to_string(ctx)?
            .to_std_string_escaped();

        unsafe {
            host_log(message.as_ptr(), message.len());
        }

        Ok(JsValue::undefined())
    });

    let console = boa_engine::object::ObjectInitializer::new(context)
        .function(log_fn, js_string!("log"), 1)
        .build();

    context
        .register_global_property(
            js_string!("console"),
            console,
            boa_engine::property::Attribute::all(),
        )
        .expect("failed to register console");
}
