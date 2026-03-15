//! Feature-gated trace system for the codegen pipeline.
//!
//! When the `trace` feature is enabled, [`trace!`] pushes structured
//! JSON events into a thread-local buffer. When disabled, the macros
//! expand to nothing — zero cost, zero code.
//!
//! Events are **tagged, not nested**. Each event carries its own context
//! (phase, block, seq) so the log is append-only and order-independent.
//! The frontend reconstructs structure from the tags.
//!
//! Ambient context (phase, block, etc.) is set via [`set_context`] and
//! automatically merged into every [`trace!`] call, so call sites stay
//! clean.
//!
//! # Usage
//!
//! ```ignore
//! use autosynth_lower::{trace, trace_do};
//!
//! // Set ambient context once at phase boundaries
//! autosynth_lower::trace::set_context("phase", "build");
//! autosynth_lower::trace::set_context("block", "User(6)");
//!
//! // Events automatically include the context
//! trace!({
//!     "type": "op",
//!     "seq": seq,
//!     "text": "v11 = sub v0, v10"
//! });
//! // → {"type":"op","seq":3,"text":"...","phase":"build","block":"User(6)"}
//!
//! // Multi-statement trace logic
//! trace_do! {
//!     let snapshot = state.to_json();
//!     trace!({ "type": "snapshot", "seq": seq, "state": snapshot });
//! }
//! ```

#[cfg(feature = "trace")]
use std::cell::{Cell, RefCell};

#[cfg(feature = "trace")]
thread_local! {
    static EVENTS: RefCell<Vec<serde_json::Value>> = const { RefCell::new(Vec::new()) };
    static SEQ: Cell<u32> = const { Cell::new(0) };
    static CONTEXT: RefCell<serde_json::Map<String, serde_json::Value>> =
        RefCell::new(serde_json::Map::new());
}

/// Get the next monotonic sequence number.
#[cfg(feature = "trace")]
pub fn next_seq() -> u32 {
    SEQ.with(|s| {
        let v = s.get();
        s.set(v + 1);
        v
    })
}

/// Set an ambient context field that gets merged into every subsequent
/// [`trace!`] call.
///
/// Use at phase/block boundaries to avoid repeating context on every event.
#[cfg(feature = "trace")]
pub fn set_context(key: &str, value: impl Into<serde_json::Value>) {
    CONTEXT.with(|ctx| {
        ctx.borrow_mut().insert(key.to_string(), value.into());
    });
}

/// Remove an ambient context field.
#[cfg(feature = "trace")]
pub fn clear_context(key: &str) {
    CONTEXT.with(|ctx| {
        ctx.borrow_mut().remove(key);
    });
}

/// Remove all ambient context fields.
#[cfg(feature = "trace")]
pub fn clear_all_context() {
    CONTEXT.with(|ctx| ctx.borrow_mut().clear());
}


/// Push a trace event into the thread-local buffer.
///
/// Merges ambient context fields into the event. Event fields take
/// precedence over context (so you can override context per-event).
#[cfg(feature = "trace")]
pub fn push(mut value: serde_json::Value) {
    CONTEXT.with(|ctx| {
        if let serde_json::Value::Object(map) = &mut value {
            for (k, v) in ctx.borrow().iter() {
                // Don't overwrite fields explicitly set on the event
                map.entry(k.clone()).or_insert_with(|| v.clone());
            }
        }
    });
    EVENTS.with(|e| e.borrow_mut().push(value));
}

/// Drain all trace events from the thread-local buffer.
#[cfg(feature = "trace")]
pub fn take_trace() -> Vec<serde_json::Value> {
    EVENTS.with(|e| std::mem::take(&mut *e.borrow_mut()))
}

/// Clear the thread-local buffer, reset the sequence counter, and
/// clear all ambient context.
#[cfg(feature = "trace")]
pub fn reset() {
    EVENTS.with(|e| e.borrow_mut().clear());
    SEQ.with(|s| s.set(0));
    clear_all_context();
}

/// Set an ambient context field. Compiles to nothing when trace is disabled.
///
/// ```ignore
/// trace_ctx!("phase", "build");
/// trace_ctx!("block", format!("{block_id:?}"));
/// ```
#[cfg(feature = "trace")]
#[macro_export]
macro_rules! trace_ctx {
    ($key:expr, $val:expr) => {
        $crate::trace::set_context($key, $val)
    };
}

#[cfg(not(feature = "trace"))]
#[macro_export]
macro_rules! trace_ctx {
    ($key:expr, $val:expr) => {};
}

/// Clear an ambient context field. Compiles to nothing when trace is disabled.
#[cfg(feature = "trace")]
#[macro_export]
macro_rules! trace_ctx_clear {
    ($key:expr) => {
        $crate::trace::clear_context($key)
    };
}

#[cfg(not(feature = "trace"))]
#[macro_export]
macro_rules! trace_ctx_clear {
    ($key:expr) => {};
}

/// Emit a single JSON trace event.
///
/// Ambient context fields are merged in automatically. Compiles to
/// nothing when the `trace` feature is disabled.
///
/// ```ignore
/// trace!({
///     "type": "op",
///     "seq": seq,
///     "text": format!("v{} = add v{}, v{}", dst, lhs, rhs)
/// });
/// ```
#[cfg(feature = "trace")]
#[macro_export]
macro_rules! trace {
    ($($tt:tt)*) => {
        $crate::trace::push($crate::__serde_json::json!($($tt)*))
    };
}

#[cfg(not(feature = "trace"))]
#[macro_export]
macro_rules! trace {
    ($($tt:tt)*) => {};
}

/// Run a block of code only when the `trace` feature is enabled.
///
/// Use this for multi-statement trace logic (e.g. expensive snapshot
/// serialization) that should compile to nothing in release.
///
/// ```ignore
/// trace_do! {
///     let snapshot = regalloc.snapshot_json();
///     trace!({ "type": "snapshot", "state": snapshot });
/// }
/// ```
#[cfg(feature = "trace")]
#[macro_export]
macro_rules! trace_do {
    ($($body:tt)*) => { $($body)* };
}

#[cfg(not(feature = "trace"))]
#[macro_export]
macro_rules! trace_do {
    ($($body:tt)*) => {};
}
