/// Unified context for JIT execution — used in both fiber and non-fiber modes.
///
/// Field offsets must match the CTX_* constants in lower_aarch64.rs.
/// The layout is tightly coupled to generated machine code: the lowerer
/// emits loads/stores at hard-coded offsets into this struct.
#[repr(C)]
pub struct JitContext {
    pub func_table: u64,   //   0: unused (kept for offset stability)
    pub wasm_sp: u64,      //   8: wasm stack pointer
    pub stack_base: u64,   //  16: wasm stack base
    pub is_fiber: u64,     //  24: 0 = non-fiber, nonzero = fiber
    pub resume_lr: u64,    //  32: resume point (fiber only)
    pub jit_sp: u64,       //  40: JIT native SP (fiber only)
    pub saved_fuel: u64,   //  48: x21 (fuel)
    pub saved_fp: u64,     //  56: x29 (locals base)
    pub host_sp: u64,      //  64: host SP
    pub host_fp: u64,      //  72: host x29
    pub host_lr: u64,      //  80: host x30
    pub host_ctx: u64,     //  88: host x20
    pub wasm_sp_off: u64,  //  96: result offset (completion)
    pub scratch: [u64; 7], // 104: x9-x15 (56 bytes)
}
// Total: 160 bytes

impl JitContext {
    pub fn new() -> Self {
        // Safety: all-zeros is a valid initial state (unused until entry).
        unsafe { std::mem::zeroed() }
    }
}
