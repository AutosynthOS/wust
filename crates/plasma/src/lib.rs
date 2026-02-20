#![cfg_attr(target_arch = "wasm32", no_std)]
extern crate alloc;

/// Dummy getrandom backend for `wasm32-unknown-unknown`.
///
/// Boa's dependency chain pulls in `getrandom`, but we don't need
/// cryptographic randomness in the embedded JS runtime. This fills
/// the buffer with zeros, which is sufficient for non-security uses.
///
/// Activated by building with `--cfg getrandom_backend="custom"`.
#[cfg(target_arch = "wasm32")]
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

use alloc::collections::VecDeque;
use alloc::rc::Rc;
use alloc::string::ToString;
use boa_engine::builtins::promise::PromiseState;
use boa_engine::job::{Job, JobExecutor};
use boa_engine::module::{ModuleLoader, Referrer};
use boa_engine::native_function::NativeFunction;
use boa_engine::{Context, JsArgs, JsError, JsResult, JsValue, Module, Source, js_string};
use core::cell::RefCell;

// --- host_log: wasm import on wasm32, eprintln on native ---

#[cfg(target_arch = "wasm32")]
#[link(wasm_import_module = "$root")]
unsafe extern "C" {
    #[link_name = "host-log"]
    fn host_log(ptr: *const u8, len: usize);
}

#[cfg(not(target_arch = "wasm32"))]
unsafe fn host_log(ptr: *const u8, len: usize) {
    let bytes = unsafe { core::slice::from_raw_parts(ptr, len) };
    let s = core::str::from_utf8(bytes).unwrap_or("<invalid utf-8>");
    eprintln!("[plasma] {s}");
}

// --- alloc export (wasm only) ---

#[cfg(target_arch = "wasm32")]
#[unsafe(no_mangle)]
pub extern "C" fn alloc(size: usize) -> *mut u8 {
    let layout = alloc::alloc::Layout::from_size_align(size, 1).expect("invalid layout");
    unsafe { alloc::alloc::alloc(layout) }
}

/// Synchronous job executor for environments where `futures_lite::block_on`
/// is not available (e.g. wasm32).
///
/// Drains promise and generic jobs in a loop until no more remain.
/// Async jobs and timeout jobs are dropped.
struct SyncJobExecutor {
    promise_jobs: RefCell<VecDeque<boa_engine::job::PromiseJob>>,
    generic_jobs: RefCell<VecDeque<boa_engine::job::GenericJob>>,
}

impl SyncJobExecutor {
    fn new() -> Self {
        Self {
            promise_jobs: RefCell::new(VecDeque::new()),
            generic_jobs: RefCell::new(VecDeque::new()),
        }
    }
}

impl JobExecutor for SyncJobExecutor {
    fn enqueue_job(self: Rc<Self>, job: Job, _context: &mut Context) {
        match job {
            Job::PromiseJob(p) => self.promise_jobs.borrow_mut().push_back(p),
            Job::GenericJob(g) => self.generic_jobs.borrow_mut().push_back(g),
            Job::AsyncJob(_) | Job::TimeoutJob(_) => {}
            _ => {}
        }
    }

    fn run_jobs(self: Rc<Self>, context: &mut Context) -> JsResult<()> {
        loop {
            let promise_job = self.promise_jobs.borrow_mut().pop_front();
            if let Some(job) = promise_job {
                job.call(context)?;
                continue;
            }

            let generic_job = self.generic_jobs.borrow_mut().pop_front();
            if let Some(job) = generic_job {
                job.call(context)?;
                continue;
            }

            break;
        }
        Ok(())
    }
}

/// Module loader that provides `import.meta.require` for Bun-bundled ESM.
///
/// When boa encounters `import.meta`, this loader injects a `require`
/// property that delegates to the global `require()` polyfill, enabling
/// Bun's `var __require = import.meta.require;` pattern.
struct PlasmaModuleLoader;

impl ModuleLoader for PlasmaModuleLoader {
    async fn load_imported_module(
        self: Rc<Self>,
        _referrer: Referrer,
        request: boa_engine::module::ModuleRequest,
        _context: &RefCell<&mut Context>,
    ) -> JsResult<Module> {
        let specifier = request.specifier().to_std_string_escaped();
        Err(JsError::from_opaque(JsValue::from(js_string!(
            alloc::format!("Cannot resolve module '{specifier}' — dynamic imports not supported")
        ))))
    }

    fn init_import_meta(
        self: Rc<Self>,
        import_meta: &boa_engine::JsObject,
        _module: &Module,
        context: &mut Context,
    ) {
        let require_fn = context
            .global_object()
            .get(js_string!("require"), context)
            .unwrap_or(JsValue::undefined());
        let _ = import_meta.set(js_string!("require"), require_fn, false, context);

        let _ = import_meta.set(
            js_string!("url"),
            JsValue::from(js_string!("file:///plasma/main.mjs")),
            false,
            context,
        );
    }
}

/// Evaluate a JS source string as an ES module.
///
/// Sets up polyfills, parses as ESM, evaluates, and returns `0` on
/// success or `1` on error. Errors are logged via `host_log`.
pub fn eval_source(source: &str) -> i32 {
    let loader = Rc::new(PlasmaModuleLoader);
    let executor = Rc::new(SyncJobExecutor::new());
    let mut context = match Context::builder()
        .module_loader(loader)
        .job_executor(executor)
        .build()
    {
        Ok(ctx) => ctx,
        Err(e) => {
            log_str(&alloc::format!("failed to build context: {e}"));
            return 1;
        }
    };
    register_console(&mut context);
    log_str("[eval] registering polyfills");
    modules::register_modules(&mut context);

    log_str("[eval] parsing module");
    let module = match Module::parse(Source::from_bytes(source.as_bytes()), None, &mut context) {
        Ok(m) => m,
        Err(e) => {
            log_error(&e);
            return 1;
        }
    };

    log_str("[eval] load_link_evaluate");
    let promise = module.load_link_evaluate(&mut context);
    log_str("[eval] running jobs");
    if let Err(e) = context.run_jobs() {
        log_str(&alloc::format!("job queue error: {e}"));
        return 1;
    }

    match promise.state() {
        PromiseState::Fulfilled(_) => 0,
        PromiseState::Rejected(err_value) => {
            let js_error = JsError::from_opaque(err_value);
            log_error(&js_error);
            1
        }
        PromiseState::Pending => {
            log_str("module evaluation still pending after run_jobs");
            1
        }
    }
}

/// Wasm entry point — reads a UTF-8 string from linear memory and evaluates it.
#[cfg(target_arch = "wasm32")]
#[unsafe(no_mangle)]
pub extern "C" fn eval(ptr: *const u8, len: usize) -> i32 {
    let source = unsafe { core::slice::from_raw_parts(ptr, len) };
    let source = match core::str::from_utf8(source) {
        Ok(s) => s,
        Err(_) => return 1,
    };
    eval_source(source)
}

/// Logs a JS error to the host via `host_log`.
fn log_error(e: &JsError) {
    let msg = e.to_string();
    unsafe {
        host_log(msg.as_ptr(), msg.len());
    }
}

/// Logs a plain string to the host via `host_log`.
pub(crate) fn log_str(msg: &str) {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hello_world() {
        let result = eval_source("console.log('hello from native plasma')");
        assert_eq!(result, 0);
    }

    #[test]
    fn test_builtins() {
        let result = eval_source(
            r#"
            const checks = [
                ['Map', typeof Map],
                ['Set', typeof Set],
                ['WeakMap', typeof WeakMap],
                ['WeakSet', typeof WeakSet],
                ['WeakRef', typeof WeakRef],
                ['FinalizationRegistry', typeof FinalizationRegistry],
                ['Promise', typeof Promise],
                ['Proxy', typeof Proxy],
                ['Reflect', typeof Reflect],
            ];
            for (const [name, t] of checks) {
                console.log(name + ': ' + t);
            }
        "#,
        );
        assert_eq!(result, 0);
    }

    const BENCH_JS: &str = r#"
let sum = 0;
for (let i = 0; i < 100000; i++) {
    sum += i * i;
}
console.log('sum=' + sum);
"#;

    #[test]
    fn bench_loop_native() {
        let start = std::time::Instant::now();
        let result = eval_source(BENCH_JS);
        let elapsed = start.elapsed();
        eprintln!("native: result={result}, elapsed={elapsed:?}");
        assert_eq!(result, 0);
    }

    #[test]
    #[ignore] // stack overflow — boa's parser recurses too deep on 37K-line bundle
    fn test_discord_bundle() {
        let bundle = include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../plasma_hello/discord-bot/bundle.js"
        ));
        let start = std::time::Instant::now();
        let result = eval_source(bundle);
        let elapsed = start.elapsed();
        eprintln!("discord bundle: result={result}, elapsed={elapsed:?}");
    }
}
