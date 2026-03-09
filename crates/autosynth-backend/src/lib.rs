//! Common traits for backend instruction emitters.
//!
//! A backend is responsible for **instruction selection only** — it picks
//! which machine instructions to emit for a given IR operation. It does
//! NOT manage register allocation, spilling, or materialization decisions.
//!
//! The backend receives operands and resolves them through the
//! [`LowerCtx`] (via `autosynth-lower` resolution functions), then
//! encodes the result into machine code bytes.

use autosynth_isa::PReg;
use autosynth_lower::LowerCtx;
use smallvec::SmallVec;

pub struct MachineConfig {
    pub pool: Vec<PReg>,
}

impl MachineConfig {
    pub fn new(pool: Vec<PReg>) -> Self {
        Self { pool }
    }
}

/// A backend that can encode IR instructions into machine code.
pub trait BackendEmitter {
    fn machine_config() -> MachineConfig;
    /// Encode a single IR instruction into machine code.
    ///
    /// The backend resolves operands through `ctx` (folding immediates
    /// or requesting physical registers) and emits the resulting bytes
    /// via `ctx.emit_code()`.
    fn emit(
        ctx: &mut impl LowerCtx,
        inst: autosynth_ir::IrInst,
    ) -> Result<SmallVec<[u8; 8]>, String>;
}
