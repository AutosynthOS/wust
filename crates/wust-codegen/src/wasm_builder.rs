use std::collections::BTreeMap;

use autosynth_codegen::builder::{FunctionBuilder, VRegOrRef};
use autosynth_ir::{AluOp, BlockId, CompOp, Operand, VCode, VRegState};
use autosynth_isa::{IsaReg, PReg, Width};
use autosynth_regalloc::MachineConfig;
use wust_core::{FRAME_HEADER_SIZE, FuncMeta};

use crate::conversion::val_width;
use crate::region::StackRegion;
use crate::wasm_block::WasmBlock;

/// Wasm-aware function builder.
pub struct WasmFunctionBuilder {
    meta: FuncMeta,
    pub inner: FunctionBuilder,
    blocks: BTreeMap<BlockId, WasmBlock>,
}

/// ## Wasm ABI Stack Design
///
/// ┌─────────┬─────────┐ ← g_lb + 0
/// │ param 0 │ param 1 │
/// │  (i32)  │  (i32)  │
/// ├─────────┴─────────┤ ← g_lb + 8
/// │     param 2       │
/// │      (i64)        │
/// ├─────────┬─────────┤ ← g_lb + 16
/// │ local 0 │ local 1 │
/// │  (i32)  │  (i64)  │
/// ├─────────┘         │
/// │         ┌─────────┤
/// │ ..cont  │ local 2 │
/// │         │  (i32)  │
/// ├─────────┴─────────┤ ← g_lb + 32 (locals_size)
/// │   FRAME HEADER    │
/// │    (12 bytes)     │
/// ├─────────┬─────────┤ ← g_lb + 44 (operands base)
/// │  i32    │   i32   │
/// │         │         │
/// ├─────────┼─────────┘
/// │  i32    │
/// │         │
/// └─────────┘
impl WasmFunctionBuilder {
    pub fn new(meta: &FuncMeta, config: MachineConfig) -> Self {
        let mut function = Self {
            meta: meta.clone(),
            inner: FunctionBuilder::new(config),
            blocks: BTreeMap::new(),
        };

        function.emit_host_to_jit_block();
        function.emit_jit_entry();

        function
    }

    /// ## Get an ISA Reg
    ///
    /// g_sp = IsaReg::StackPointer -> Native Fibre Stack Pointer
    /// g_lr = IsaReg::ReturnAddress -> Native Link Return Address
    /// g_lb = IsaReg::FramePointer -> WASM Locals Base Pointer
    fn isa_reg(&self, reg: IsaReg) -> PReg {
        self.inner
            .config
            .isa_reg(reg)
            .expect("expected reserveed pointer")
    }

    fn emit_jit_entry(&mut self) {
        let g_sp = self.isa_reg(IsaReg::StackPointer);
        let g_lr = self.isa_reg(IsaReg::ReturnAddress);
        let g_lb = self.isa_reg(IsaReg::FramePointer);

        let alloc = self.inner.alloc.clone();
        self.inner.start_block(BlockId::Entry(1));

        let mut locals = StackRegion::new(g_lb, 0, &alloc);
        let mut fibre = StackRegion::new(g_sp, 0, &alloc);
        let operands = StackRegion::new(
            g_lb,
            self.meta.locals_size + FRAME_HEADER_SIZE as u16,
            &alloc,
        );

        // Function parameter locals (dirty)
        // Parameters arrive in physical registers 0..N
        // With their memory stack slots defined as dirty
        for (i, param) in self.meta.params.iter().enumerate() {
            let vreg = locals.push_define(VRegState {
                preg: Some(PReg(i as u8)),
                dirty: true,
                ..VRegState::new(val_width(param))
            });
            self.inner.emit(VCode::Define(vreg));
        }

        // Zero-initialized locals
        // - Initialized to const 0
        // - Memory slot is dirty
        for local in self.meta.locals.iter() {
            let vreg = locals.push_define(VRegState {
                r#const: Some(0),
                dirty: true,
                ..VRegState::new(val_width(local))
            });
            self.inner.emit(VCode::Define(vreg));
        }

        // push link-register onto the fibre stack
        let lr_vreg = fibre.push_define(VRegState {
            // link register is set by CPU on
            // branch-link/function call operation.
            preg: Some(g_lr),
            // we must store this value into the
            // fibre stack if it's ever about to be
            // cloberred by a call
            dirty: true,
            // this value always must end up in the return
            // address register
            target: Some(g_lr),
            ..VRegState::new(Width::W64)
        });
        self.inner.emit(VCode::Define(lr_vreg));

        let jit_entry = self.inner.block(BlockId::Entry(1));
        self.blocks.insert(
            BlockId::Entry(1),
            WasmBlock::new(
                BTreeMap::from([("locals", locals), ("operands", operands), ("fibre", fibre)]),
                &jit_entry,
                &alloc,
            ),
        );
    }

    fn emit_host_to_jit_block(&mut self) {
        let g_sp = self.isa_reg(IsaReg::StackPointer);
        let g_lr = self.isa_reg(IsaReg::ReturnAddress);
        let g_lb = self.isa_reg(IsaReg::FramePointer);

        let alloc_rc = self.inner.alloc.clone();

        // --- Entry(0): host trampoline ---
        // Params on managed stack (clean — host put them there).
        self.start_block(BlockId::Entry(0));
        let mut params = StackRegion::new(g_lb, 0, &alloc_rc);
        let mut fibre = StackRegion::new(g_sp, 0, &alloc_rc);

        for (i, param) in self.meta.params.iter().enumerate() {
            let vreg = params.push_define(VRegState {
                // host places function parameters into
                // their canonical wasm abi stack locations
                dirty: false,
                // jit call expects function parameters in
                // registers 0..N for function calls
                target: Some(PReg(i as u8)),
                ..VRegState::new(val_width(param))
            });
            self.inner.emit(VCode::Define(vreg));
        }

        // Push return address onto fibre stack
        let lr_vreg = fibre.push_define(VRegState {
            preg: Some(g_lr),
            target: Some(g_lr),
            dirty: true,
            ..VRegState::new(Width::W64)
        });
        self.inner.emit(VCode::Define(lr_vreg));

        // --- prepare for call --
        // ensure params in target
        while let Some(vreg_or_ref) = params.pop() {
            let vreg = self.inner.resolve(vreg_or_ref);
            self.inner.push_operand(vreg);
            self.inner.emit(VCode::Materialize);
            self.inner.emit(VCode::Operand(Operand::DstVReg(vreg)));
        }

        // clobber fibre vregs
        while let Some(vreg_or_ref) = fibre.pop() {
            self.inner.push_operand(vreg_or_ref);
            self.inner.emit(VCode::Clobber);
        }

        // decrement stack pointer
        self.inner.emit(VCode::Operand(Operand::PReg(g_sp))); // lhs register
        self.inner.emit(VCode::Operand(Operand::Const(16))); // rhs
        self.inner.emit(VCode::Alu { op: AluOp::Sub });
        self.inner
            .emit(VCode::Operand(Operand::DstPReg(g_sp, Width::W64)));

        let host_to_jit = self.inner.block(BlockId::Entry(0));
        self.blocks.insert(
            BlockId::Entry(0),
            WasmBlock::new(
                BTreeMap::from([("params", params), ("fibre", fibre)]),
                &host_to_jit,
                &alloc_rc,
            ),
        );
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
        let local = self.region_ref("locals").get(idx);
        let source = self.inner.resolve(*local);
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
