#![cfg(feature = "trace")]

use autosynth_lower::{trace, trace_ctx, trace_do};

#[test]
fn trace_basic_events() {
    autosynth_lower::trace::reset();

    trace_ctx!("phase", "build");
    trace_ctx!("block", "User(6)");

    trace!({
        "type": "op",
        "seq": autosynth_lower::trace::next_seq(),
        "text": "v0 = param"
    });

    trace!({
        "type": "op",
        "seq": autosynth_lower::trace::next_seq(),
        "text": "v1 = const 1"
    });

    let events = autosynth_lower::trace::take_trace();
    assert_eq!(events.len(), 2);

    // Both events should have context merged in
    assert_eq!(events[0]["phase"], "build");
    assert_eq!(events[0]["block"], "User(6)");
    assert_eq!(events[0]["type"], "op");
    assert_eq!(events[0]["seq"], 0);
    assert_eq!(events[0]["text"], "v0 = param");

    assert_eq!(events[1]["seq"], 1);
    assert_eq!(events[1]["phase"], "build");
}

#[test]
fn trace_context_override() {
    autosynth_lower::trace::reset();

    trace_ctx!("phase", "build");

    // Event can override context
    trace!({
        "type": "op",
        "phase": "regalloc"
    });

    let events = autosynth_lower::trace::take_trace();
    assert_eq!(events[0]["phase"], "regalloc");
}

#[test]
fn trace_do_block() {
    autosynth_lower::trace::reset();

    let mut ran = false;
    trace_do! {
        ran = true;
        trace!({"type": "snapshot"});
    }

    assert!(ran);
    assert_eq!(autosynth_lower::trace::take_trace().len(), 1);
}
