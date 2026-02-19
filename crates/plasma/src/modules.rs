/// Registers Node.js polyfills and the `require()` module system into
/// a boa JS context.
///
/// Evaluates polyfill JS strings in dependency order so that globals like
/// `EventEmitter`, `Buffer`, and `process` are available before the
/// `require()` registry references them.
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
    polyfills::require,
];

/// Initialize the boa context with all Node.js polyfills and require().
///
/// Evaluates each polyfill JS string in order. If any polyfill fails
/// to evaluate, logs the error via `host_log` and continues — this
/// allows partial initialization for debugging.
pub fn register_modules(context: &mut Context) {
    for source_fn in POLYFILL_SOURCES {
        let js = source_fn();
        if let Err(e) = context.eval(Source::from_bytes(js)) {
            crate::log_error(&e);
        }
    }
}
