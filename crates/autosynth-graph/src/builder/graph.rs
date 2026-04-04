//! WasmGraph — the builder's output, handed to the compiler.

use slotmap::SlotMap;

use crate::builder::function::WasmFunctionBuilder;
use crate::types::{Input, VInit, VRegKey};

/// The finalized builder output.
pub struct WasmGraph {
    pub ops: slotmap::SlotMap<crate::types::OpKey, crate::types::Operation>,
    pub vregs: SlotMap<VRegKey, VInit>,
}

impl From<WasmFunctionBuilder> for WasmGraph {
    fn from(func: WasmFunctionBuilder) -> Self {
        let mut state = func.into_state();

        // Resolve all Input::VRef → Input::VReg
        for (_, op) in state.operations.iter_mut() {
            for input in op.inputs.iter_mut() {
                if let Input::VRef(ref_key) = input {
                    if let Some(&vreg_key) = state.vreg_refs.get(*ref_key) {
                        *input = Input::VReg(vreg_key);
                    }
                }
            }
        }

        WasmGraph {
            ops: state.operations,
            vregs: state.vreg_defs,
        }
    }
}
