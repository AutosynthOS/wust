//! Wasm block — named regions + effect chain.

use std::collections::BTreeMap;

use autosynth_isa::{PReg, Width};
use smallvec::{SmallVec, smallvec};
use wust_core::{FuncIdx, FuncMeta, ValType};

use crate::builder::BlockId;
use crate::builder::region::BuilderRegion;
use crate::builder::state::SharedBuildState;
use crate::types::{Abi, OpKey, valtype_width};
use crate::{AluOp, Input, Operation, VCode, VInit, VRegKey};

const G_LB: PReg = PReg(29);
const G_SP: PReg = PReg(31);

/// Per-block wasm state: named regions + effect chain.
/// Cloning snapshots the state for branching.
#[derive(Debug, Clone)]
pub(crate) struct WasmBlock {
    pub(crate) regions: BTreeMap<&'static str, BuilderRegion>,
    pub(crate) last_effect: Option<OpKey>,
    pub(crate) operations: Vec<OpKey>,
    pub(crate) state: SharedBuildState,
}

impl WasmBlock {
    pub(crate) fn fresh(state: &SharedBuildState, operand_base: u16) -> Self {
        Self {
            state: state.clone(),
            operations: Vec::new(),
            regions: BTreeMap::from([
                ("locals", BuilderRegion::new(G_LB, 0, &state)),
                ("operands", BuilderRegion::new(G_LB, operand_base, &state)),
                ("fibre", BuilderRegion::new(G_SP, 0, &state)),
            ]),
            last_effect: None,
        }
    }

    pub(crate) fn region(&mut self, name: &str) -> &mut BuilderRegion {
        self.regions.get_mut(name).expect(name)
    }

    pub(crate) fn emit_with_key(&mut self, fn_cb: impl FnOnce(OpKey) -> Operation) -> OpKey {
        let mut state = self.state.borrow_mut();

        let key = state.operations.insert_with_key(|op_key| Operation {
            effect: self.last_effect,
            prev: self.operations.last().copied(),
            ..fn_cb(op_key)
        });
        self.operations.push(key);
        key
    }

    pub(crate) fn emit(&mut self, operation: Operation) -> OpKey {
        self.emit_with_key(|_| operation)
    }

    pub(crate) fn define_op(&mut self, init: VInit) -> Input {
        let defined = self.state.borrow_mut().define(init);

        self.emit(Operation {
            opcode: VCode::Define,
            effect: None,
            prev: None,
            inputs: SmallVec::new(),
            defines: smallvec![self.state.borrow().unwrap_as_def_key(&defined)],
        });

        defined
    }

    pub(crate) fn define_and_push(&mut self, region: &str, init: VInit) {
        let ref_key = self.define_op(init);
        self.push_vreg(region, ref_key);
    }

    pub(crate) fn push_vreg(&mut self, region: &str, vreg: Input) {
        let region = self.region(region);
        let operation = region.push(vreg);
        self.emit(operation);
    }

    pub(crate) fn push_local_get(&mut self, local: usize, expected_width: Width) {
        let (local_ref, local_width) = self.region("locals").get_index(local);
        assert_eq!(local_width, expected_width);
        self.push_vreg("operands", local_ref);
    }

    pub(crate) fn pop(&mut self, region: &str) -> (Input, Width) {
        let (op, value, width) = self.region(region).pop();

        self.emit(Operation {
            effect: self.last_effect,
            prev: self.operations.last().copied(),
            ..op
        });

        (value, width)
    }

    pub(crate) fn pop_expect_width(&mut self, region: &str, width: Width) -> Input {
        let (value, actual_width) = self.pop(region);
        assert_eq!(width, actual_width);
        value
    }

    pub(crate) fn binop(&mut self, op: AluOp, width: Width) {
        let lhs_ref = self.pop_expect_width("operands", width);
        let rhs_ref = self.pop_expect_width("operands", width);
        let dst = self.state.borrow_mut().define(VInit {
            width: width,
            constant: None,
            preg: None,
            mem: None,
        });

        let dst_key = self.state.borrow_mut().unwrap_as_def_key(&dst);

        let op_key = self.emit(Operation {
            opcode: VCode::Alu(op),
            inputs: smallvec![lhs_ref, rhs_ref],
            defines: smallvec![dst_key],
            effect: None,
            prev: None,
        });

        // self.state
        //     .borrow_mut()
        //     .vreg_defs
        //     .get_mut(dst_key)
        //     .unwrap()
        //     .from_op = Some(op_key);

        self.push_vreg("operands", dst);
    }

    pub(crate) fn pop_local_set(&mut self, local: usize, expected_width: Width) {
        let val = self.pop_expect_width("operands", expected_width);
        let op = self
            .region("locals")
            .set_index_expect_width(local, val, expected_width);
        self.emit(Operation {
            prev: self.operations.last().copied(),
            effect: self.last_effect,
            ..op
        });
    }

    /// Finalize this block's regions (convert VReg→VRef) and fork into a new block.
    /// The new block gets cloned regions + shared state, empty ops, and
    /// last_effect set to `branch_op`.
    pub(crate) fn finalize_and_fork(&mut self, branch_op: OpKey) -> WasmBlock {
        // 1. Convert all Input::VReg entries to Input::VRef
        for region in self.regions.values_mut() {
            region.convert_vregs_to_vrefs();
        }

        // 2. Clone regions + state
        let forked = WasmBlock {
            regions: self.regions.clone(),
            last_effect: Some(branch_op),
            operations: Vec::new(),
            state: self.state.clone(),
        };

        forked
    }

    pub(crate) fn emit_call(
        &mut self,
        func_idx: FuncIdx,
        funcs: &[FuncMeta],
        label: BlockId,
        abi: Abi,
    ) {
        let callee = &funcs[*func_idx as usize];

        // Pop args (rightmost first)
        let inputs = self.pop_valtypes::<SmallVec<_>>(&callee.params);

        // Define result vregs — each arrives in PReg(i) per ABI
        let result_defs: SmallVec<[VRegKey; 1]> = callee
            .results
            .iter()
            .enumerate()
            .map(|(i, ty)| {
                let input = self.define_op(VInit {
                    width: valtype_width(*ty),
                    constant: None,
                    preg: Some(PReg(i as u8)),
                    mem: None,
                });
                self.state.borrow().unwrap_as_def_key(&input)
            })
            .collect();

        // Emit the call
        let call_key = self.emit(Operation {
            opcode: VCode::Call {
                func_idx,
                label,
                abi,
            },
            inputs,
            defines: result_defs.clone(),
            effect: self.last_effect,
            prev: self.operations.last().copied(),
        });

        self.last_effect = Some(call_key);

        // Set from_op on each result vreg
        // for &vreg_key in &result_defs {
        //     self.state
        //         .borrow_mut()
        //         .vreg_defs
        //         .get_mut(vreg_key)
        //         .unwrap()
        //         .from_op = Some(call_key);
        // }

        // Push results onto operands
        for &vreg_key in &result_defs {
            self.push_vreg("operands", Input::VReg(vreg_key));
        }
    }

    pub(crate) fn pop_valtypes<C: FromIterator<Input>>(&mut self, types: &[ValType]) -> C {
        types
            .iter()
            .rev()
            .map(|ty| self.pop_expect_width("operands", valtype_width(*ty)))
            .collect()
    }
}
