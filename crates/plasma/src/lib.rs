use boa_engine::{Context, Source, JsValue, js_string, JsArgs};
use boa_engine::native_function::NativeFunction;

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
    let layout = std::alloc::Layout::from_size_align(size, 1)
        .expect("invalid layout");
    unsafe { std::alloc::alloc(layout) }
}

/// Evaluates a UTF-8 JS source string located at `ptr` with length `len`.
///
/// Returns `0` on success, `1` on error.
#[unsafe(no_mangle)]
pub extern "C" fn eval(ptr: *const u8, len: usize) -> i32 {
    let source = unsafe { std::slice::from_raw_parts(ptr, len) };
    let source = match std::str::from_utf8(source) {
        Ok(s) => s,
        Err(_) => return 1,
    };

    let mut context = Context::default();
    register_console(&mut context);

    match context.eval(Source::from_bytes(source)) {
        Ok(_) => 0,
        Err(_) => 1,
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
        .register_global_property(js_string!("console"), console, boa_engine::property::Attribute::all())
        .expect("failed to register console");
}
