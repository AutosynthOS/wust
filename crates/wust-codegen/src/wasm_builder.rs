use std::collections::BTreeMap;

use autosynth_codegen::builder::{FunctionBuilder, VRegOrRef};
use autosynth_ir::{AluOp, BlockId, CompOp, Operand, VCode, VRegState};
use autosynth_isa::{PReg, Width};
use autosynth_regalloc::MachineConfig;
use wust_core::{FRAME_HEADER_SIZE, FuncMeta};

use crate::conversion::val_width;
use crate::region::StackRegion;
use crate::wasm_block::WasmBlock;

/// Wasm-aware function builder.
pub struct WasmFunctionBuilder {
    pub inner: FunctionBuilder,
    blocks: BTreeMap<BlockId, WasmBlock>,
}

impl WasmFunctionBuilder {
    pub fn new(func: &FuncMeta, mut config: MachineConfig) -> Self {
        let g_lb = config.isa_reg(autosynth_isa::IsaReg::FramePointer).expect("no frame pointer");
        let g_sp = config.isa_reg(autosynth_isa::IsaReg::StackPointer).expect("no stack pointer");

        let mut inner = FunctionBuilder::new(config);
        let mut blocks = BTreeMap::new();

        let alloc_rc = inner.alloc.clone();

        // --- Entry(0): host trampoline ---
        // Params on managed stack (clean — host put them there).
        {
            inner.start_block(BlockId::Entry(0));
            let mut params = StackRegion::new(g_lb, 0, &alloc_rc);
            for param in func.params.iter() {
                let vreg = params.push_define(VRegState::new(val_width(param)), false);
                inner.emit(VCode::Define(vreg));
            }

            // TODO: emit trampoline VCode

            let fibre = StackRegion::new(g_sp, 0, &alloc_rc);
            let entry0_block = inner.block(BlockId::Entry(0));
            blocks.insert(
                BlockId::Entry(0),
                WasmBlock::new(
                    BTreeMap::from([("params", params), ("fibre", fibre)]),
                    &entry0_block,
                    &alloc_rc,
                ),
            );
        }

        // --- Entry(1): function body ---
        // Params in CC regs + stack slots (dirty). Locals const 0 + stack slots (clean).
        {
            inner.start_block(BlockId::Entry(1));
            let mut locals = StackRegion::new(g_lb, 0, &alloc_rc);
            for (i, param) in func.params.iter().enumerate() {
                let vreg = locals.push_define(
                    VRegState {
                        preg: Some(PReg(i as u8)),
                        ..VRegState::new(val_width(param))
                    },
                    true,
                );
                inner.emit(VCode::Define(vreg));
            }
            for local in func.locals.iter() {
                let vreg = locals.push_define(
                    VRegState {
                        r#const: Some(0),
                        ..VRegState::new(val_width(local))
                    },
                    true,
                );
                inner.emit(VCode::Define(vreg));
            }
            let locals_header_size = func.locals_size as u32 + FRAME_HEADER_SIZE as u32;
            let operands = StackRegion::new(g_lb, locals_header_size, &alloc_rc);
            let fibre = StackRegion::new(g_sp, 0, &alloc_rc);
            let entry1_block = inner.block(BlockId::Entry(1));
            blocks.insert(
                BlockId::Entry(1),
                WasmBlock::new(
                    BTreeMap::from([("locals", locals), ("operands", operands), ("fibre", fibre)]),
                    &entry1_block,
                    &alloc_rc,
                ),
            );
        }

        Self { inner, blocks }
    }

    fn current_id(&self) -> BlockId {
        self.inner.current_block_id()
    }

    fn current(&mut self) -> &mut WasmBlock {
        let id = self.current_id();
        self.blocks.get_mut(&id).expect("no current wasm block")
    }

    fn region(&mut self, name: &str) -> &mut StackRegion {
        self.current().region(name)
    }

    fn region_ref(&self, name: &str) -> &StackRegion {
        let id = self.inner.current_block_id();
        self.blocks[&id].region_ref(name)
    }

    // --- Region operations ---

    pub fn push_const(&mut self, val: i64, width: Width) {
        let id = self.inner.define(VRegState {
            r#const: Some(val),
            ..VRegState::new(width)
        });
        self.region("operands").push(VRegOrRef::VReg(id));
    }

    pub fn push_local(&mut self, idx: usize) {
        let local = self.region_ref("locals").get(idx).val;
        let source = self.inner.resolve(local);
        let width = self.inner.width(source);
        let copy = self.inner.define(VRegState {
            copy: Some(source),
            ..VRegState::new(width)
        });
        self.region("operands").push(VRegOrRef::VReg(copy));
    }

    pub fn pop(&mut self) -> VRegOrRef {
        self.region("operands")
            .pop()
            .expect("operand stack underflow")
            .val
    }

    pub fn push(&mut self, val: VRegOrRef) {
        self.region("operands").push(val);
    }

    pub fn local_set(&mut self, idx: usize, val: VRegOrRef) {
        self.region("locals").set_val(idx, val);
    }

    // --- VCode emission ---

    pub fn binop(&mut self, op: AluOp, width: Width) {
        let rhs = self.pop();
        let lhs = self.pop();
        let dst = self.inner.define(VRegState {
            inst_dst: true,
            ..VRegState::new(width)
        });

        self.inner.push_operand(lhs);
        self.inner.push_operand(rhs);
        self.inner.emit(VCode::Alu { op });
        self.inner.emit(VCode::Operand(Operand::DstVReg(dst)));

        self.region("operands").push(VRegOrRef::VReg(dst));
    }

    pub fn eqz(&mut self) {
        let val = self.pop();
        let zero = self.inner.define(VRegState {
            r#const: Some(0),
            ..VRegState::new(Width::W32)
        });
        let dst = self.inner.define(VRegState {
            inst_dst: true,
            ..VRegState::new(Width::W32)
        });

        self.inner.push_operand(val);
        self.inner.push_operand(zero);
        self.inner.emit(VCode::Alu {
            op: AluOp::Comp(CompOp::Eq),
        });
        self.inner.emit(VCode::Operand(Operand::DstVReg(dst)));

        self.region("operands").push(VRegOrRef::VReg(dst));
    }

    // --- Control flow ---

    pub fn br_if(&mut self, cond: VRegOrRef, then_block: BlockId, else_block: BlockId) {
        let zero = self.inner.define(VRegState {
            r#const: Some(0),
            ..VRegState::new(Width::W32)
        });
        self.inner.push_operand(cond);
        self.inner.push_operand(zero);
        self.inner.emit(VCode::BrIf {
            op: CompOp::Ne,
            block_if: then_block,
            block_else: else_block,
        });

        let id = self.current_id();
        self.ensure_or_merge(then_block, id);
        self.ensure_or_merge(else_block, id);
    }

    pub fn br(&mut self, target: BlockId) {
        self.inner.emit(VCode::Branch { target });

        let id = self.current_id();
        self.ensure_or_merge(target, id);
    }

    pub fn start_block(&mut self, id: BlockId) {
        self.inner.start_block(id);
    }

    pub fn emit_return(&mut self, func: &FuncMeta) {
        for (i, _) in func.results.iter().enumerate() {
            let result = self.pop();
            self.inner.set_target(result, PReg(i as u8));
        }
        self.inner.emit(VCode::Return);
    }

    pub fn build(self) -> autosynth_codegen::ir::IrFunction {
        self.inner.build()
    }

    // --- Internal ---

    fn ensure_or_merge(&mut self, target: BlockId, source: BlockId) {
        let src = &self.blocks[&source];
        if self.blocks.contains_key(&target) {
            let src_clone = src.clone();
            let existing = self.blocks.get_mut(&target).unwrap();
            existing.merge(&src_clone, source, &mut self.inner);
        } else {
            let forked = src.fork(source, &mut self.inner);
            self.blocks.insert(target, forked);
        }
    }
}
