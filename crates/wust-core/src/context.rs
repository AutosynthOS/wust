/// Runtime context passed to JIT code via a pinned register (g.ctx).
///
/// Will hold pointers and metadata needed by generated code to
/// interact with the host (e.g. save/restore state on suspend).
/// Currently empty — fields will be added as suspend/resume is
/// implemented.
#[repr(C)]
pub struct Context {}

impl Context {
    pub fn new() -> Self {
        Self {}
    }
}
