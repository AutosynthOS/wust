/// Registers Node.js polyfills and the `require()` module system into
/// a boa JS context.
///
/// Evaluates polyfill JS strings in dependency order so that globals like
/// `EventEmitter`, `Buffer`, and `process` are available before the
/// `require()` registry references them.
use alloc::format;
use boa_engine::{Context, Source};

use crate::polyfills;

/// Polyfills evaluated in order during context initialization.
///
/// Order matters: timers and EventEmitter must exist before require()
/// since the module registry references them.
const POLYFILL_SOURCES: &[fn() -> &'static str] = &[
    polyfills::process,
    polyfills::event_emitter,
    polyfills::timers,
    polyfills::text_codec,
    polyfills::buffer,
    polyfills::url,
    polyfills::legacy,
    polyfills::require,
];

/// Names for logging which polyfill is being evaluated.
const POLYFILL_NAMES: &[&str] = &[
    "process", "event_emitter", "timers", "text_codec", "buffer", "url", "legacy", "require",
];

pub fn register_modules(context: &mut Context) {
    for (i, source_fn) in POLYFILL_SOURCES.iter().enumerate() {
        let name = POLYFILL_NAMES.get(i).unwrap_or(&"unknown");
        crate::log_str(&alloc::format!("[polyfill] loading: {name}"));
        let js = source_fn();
        match context.eval(Source::from_bytes(js)) {
            Ok(_) => crate::log_str(&alloc::format!("[polyfill] ok: {name}")),
            Err(e) => {
                crate::log_str(&alloc::format!("[polyfill] FAILED: {name}"));
                crate::log_error(&e);
            }
        }
    }
}
