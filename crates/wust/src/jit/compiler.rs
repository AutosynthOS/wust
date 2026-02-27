use wust_codegen::ir::{AluOp, IrFunction, IrInst, Label, Operand, UnaryOp, VReg};
use crate::parse::body::{BlockKind, OpCode};
use crate::parse::func::ParsedFunction;

/// Open block during IR compilation — tracks label resolution.
struct OpenBlock {
    /// Block index in the blocks array (for Br/BrIf lookup).
    block_idx: u32,
    kind: BlockKind,
    /// Label to branch to when exiting this block.
    /// - Block/If: forward label (resolved at End).
    /// - Loop: backward label (header).
    label: Label,
    /// Virtual stack depth at block entry — used to restore vstack at
    /// control flow merge points (Else/End).
    vstack_depth: usize,
}

/// State for the wasm-to-IR compiler.
struct IrCompiler {
    /// The IR instruction sequence being built.
    insts: Vec<IrInst>,
    /// Parallel to `insts` — index of the parsed wasm op each IR
    /// instruction came from.
    source_ops: Vec<u32>,
    /// Index of the parsed op currently being compiled.
    current_op: u32,
    /// Virtual operand stack — tracks which VReg holds each wasm stack slot.
    vstack: Vec<VReg>,
    /// Next virtual register index.
    next_vreg: u32,
    /// Next label index.
    next_label: u32,
    /// Block stack for branch resolution.
    block_stack: Vec<OpenBlock>,
    /// Maximum vstack depth seen during compilation.
    max_vstack_depth: usize,
    /// Total number of locals (params + declared). Used to compute
    /// frame slot indices for operand stack spills.
    total_local_count: u32,
    /// Accumulated fuel cost for the current basic block. Flushed as a
    /// single FuelCheck before branches, labels, calls, and returns.
    pending_fuel: u32,
    /// Whether fuel checking is enabled.
    emit_fuel: bool,
    /// Local promotion: which VReg currently holds each local's value.
    /// `None` means the value only exists in the frame slot.
    local_vreg: Vec<Option<VReg>>,
    /// Whether the register value differs from what's in the frame slot.
    /// When true, must store to frame before any suspend point.
    frame_dirty: Vec<bool>,
}

impl IrCompiler {
    fn new(total_local_count: u32, emit_fuel: bool) -> Self {
        IrCompiler {
            insts: Vec::new(),
            source_ops: Vec::new(),
            current_op: 0,
            vstack: Vec::new(),
            next_vreg: 0,
            next_label: 0,
            block_stack: Vec::new(),
            max_vstack_depth: 0,
            total_local_count,
            pending_fuel: 0,
            emit_fuel,
            local_vreg: vec![None; total_local_count as usize],
            frame_dirty: vec![false; total_local_count as usize],
        }
    }

    fn fresh_vreg(&mut self) -> VReg {
        let v = VReg(self.next_vreg);
        self.next_vreg += 1;
        v
    }

    fn fresh_label(&mut self) -> Label {
        let l = Label(self.next_label);
        self.next_label += 1;
        l
    }

    fn vpush(&mut self, v: VReg) {
        self.vstack.push(v);
        if self.vstack.len() > self.max_vstack_depth {
            self.max_vstack_depth = self.vstack.len();
        }
    }

    /// Pop a VReg from the virtual operand stack.
    fn vpop(&mut self) -> VReg {
        self.vstack.pop().expect("virtual stack underflow (pop)")
    }

    fn vpeek(&self) -> VReg {
        *self.vstack.last().expect("virtual stack underflow (peek)")
    }

    fn emit(&mut self, inst: IrInst) {
        self.insts.push(inst);
        self.source_ops.push(self.current_op);
    }

    /// Add fuel cost for the current opcode. The cost is batched and
    /// emitted as a single FuelCheck at the next basic block boundary.
    fn accrue_fuel(&mut self, cost: u32) {
        if self.emit_fuel {
            self.pending_fuel += cost;
        }
    }

    /// Emit a FuelConsume + FuelCheck for any accumulated cost, then reset.
    /// Called at suspend points (before calls, at loop back-edges).
    /// Always flushes dirty locals to frame (canonical frame contract).
    fn flush_fuel(&mut self) {
        self.flush_dirty_locals();
        if self.pending_fuel > 0 && self.emit_fuel {
            self.emit(IrInst::FuelConsume {
                cost: self.pending_fuel,
            });
            self.emit(IrInst::FuelCheck { live_state: vec![] });
        }
        self.pending_fuel = 0;
    }

    /// Emit a bare FuelConsume (no check) for accumulated cost.
    /// Called before returns — fuel goes negative but no suspend point.
    fn flush_fuel_consume_only(&mut self) {
        if self.pending_fuel > 0 {
            self.emit(IrInst::FuelConsume {
                cost: self.pending_fuel,
            });
            self.pending_fuel = 0;
        }
    }

    /// Store all dirty locals to their canonical frame slots.
    /// Called before FuelCheck instructions (suspend points).
    fn flush_dirty_locals(&mut self) {
        for idx in 0..self.total_local_count {
            if self.frame_dirty[idx as usize] {
                if let Some(v) = self.local_vreg[idx as usize] {
                    self.insts.push(IrInst::FrameStore {
                        slot: idx,
                        src: v,
                    });
                    self.source_ops.push(self.current_op);
                    self.frame_dirty[idx as usize] = false;
                }
            }
        }
    }

    /// Collect current local VRegs as branch arguments.
    /// For locals not currently tracked (None), load from frame first.
    fn collect_local_args(&mut self) -> Vec<VReg> {
        (0..self.total_local_count)
            .map(|i| {
                if let Some(v) = self.local_vreg[i as usize] {
                    v
                } else {
                    let dst = self.fresh_vreg();
                    self.emit(IrInst::LocalGet { dst, idx: i });
                    self.local_vreg[i as usize] = Some(dst);
                    self.frame_dirty[i as usize] = false;
                    dst
                }
            })
            .collect()
    }

    /// Allocate fresh VRegs for block params (one per local).
    fn allocate_local_params(&mut self) -> Vec<VReg> {
        (0..self.total_local_count).map(|_| self.fresh_vreg()).collect()
    }

    /// Update local_vreg tracking from DefLabel block params.
    /// Marks all as dirty since canonical frame may not match.
    fn apply_local_params(&mut self, params: &[VReg]) {
        for (i, &v) in params.iter().enumerate() {
            self.local_vreg[i] = Some(v);
            self.frame_dirty[i] = true;
        }
    }

    /// Invalidate all local VReg tracking — values only exist in frame.
    /// Called after calls (registers clobbered).
    fn invalidate_locals(&mut self) {
        for idx in 0..self.total_local_count as usize {
            self.local_vreg[idx] = None;
            // frame_dirty is already false (we flushed before the call)
        }
    }

    fn emit_i32_const(&mut self, val: i32) {
        let dst = self.fresh_vreg();
        self.emit(IrInst::IConst {
            dst,
            val: val as i64,
        });
        self.vpush(dst);
    }

    fn emit_local_get(&mut self, idx: u32) {
        if let Some(v) = self.local_vreg[idx as usize] {
            // Value already in a register — reuse it, emit nothing.
            self.vpush(v);
        } else {
            // Value only in frame — load it.
            let dst = self.fresh_vreg();
            self.emit(IrInst::LocalGet { dst, idx });
            self.local_vreg[idx as usize] = Some(dst);
            self.frame_dirty[idx as usize] = false; // just loaded from frame
            self.vpush(dst);
        }
    }

    fn emit_local_set(&mut self, idx: u32) {
        let src = self.vpop();
        // Track in register, defer frame store to next flush.
        self.local_vreg[idx as usize] = Some(src);
        self.frame_dirty[idx as usize] = true;
    }

    fn emit_return(&mut self, result_count: usize) {
        let mut results = Vec::with_capacity(result_count);
        for _ in 0..result_count {
            results.push(self.vpop());
        }
        results.reverse();
        self.emit(IrInst::Return { results });
        // Any fuel accrued after a return is dead code — discard it.
        self.pending_fuel = 0;
    }

    fn emit_br(&mut self, block_idx: u32) {
        let stack_idx = self
            .block_stack
            .iter()
            .rposition(|b| b.block_idx == block_idx)
            .expect("branch target not on block stack");
        let label = self.block_stack[stack_idx].label;
        let args = self.collect_local_args();
        self.emit(IrInst::Br { label, args });
    }

    /// Flush only the values above `depth` from the virtual stack.
    ///
    /// Used at if/else merge points: stores branch results to frame
    /// operand stack slots, then truncates vstack to the given depth.
    fn flush_vstack_above(&mut self, depth: usize) {
        let base = self.total_local_count;
        let extras: Vec<VReg> = self.vstack.drain(depth..).collect();
        for (i, vreg) in extras.into_iter().enumerate() {
            self.emit(IrInst::FrameStore {
                slot: base + depth as u32 + i as u32,
                src: vreg,
            });
        }
    }

    /// Reload `count` values from frame operand stack slots into fresh VRegs.
    ///
    /// Values are at frame slots `[total_local_count + depth ..
    /// total_local_count + depth + count]`, where `depth` is the
    /// current vstack depth (i.e., the slot index where the flushed
    /// values start).
    fn reload_from_stack(&mut self, count: usize) {
        let base = self.total_local_count;
        let depth = self.vstack.len() as u32;
        for i in 0..count {
            let dst = self.fresh_vreg();
            self.emit(IrInst::FrameLoad {
                dst,
                slot: base + depth + i as u32,
            });
            self.vstack.push(dst);
        }
    }
}

/// Compile a parsed wasm function into architecture-independent IR.
///
/// Maintains a virtual operand stack at compile time. Values stay in
/// virtual registers and are only materialized to the physical wasm
/// stack at call boundaries and control flow merge points.
///
/// Fuel costs are accumulated per basic block and emitted as a single
/// FuelCheck before branches, labels, calls, and returns. This avoids
/// redundant checks between adjacent opcodes.
pub(crate) fn compile_with(
    func: &ParsedFunction,
    all_funcs: &[ParsedFunction],
    emit_fuel: bool,
) -> IrFunction {
    let mut c = IrCompiler::new(func.locals.len() as u32, emit_fuel);

    // Params start in registers (x9, x10, ...) via ParamDef.
    // Track them as local VRegs — they're dirty (not yet in frame).
    // Frame stores are deferred to the first flush_dirty_locals().
    for i in 0..func.param_count as u32 {
        let v = c.fresh_vreg();
        c.emit(IrInst::ParamDef { dst: v, idx: i });
        c.local_vreg[i as usize] = Some(v);
        c.frame_dirty[i as usize] = true;
    }

    // Non-param locals start as zero. Track a zero VReg — dirty
    // (frame stores deferred to first flush).
    let extra_locals = func.locals.len() as u32 - func.param_count as u32;
    if extra_locals > 0 {
        let v_zero = c.fresh_vreg();
        c.emit(IrInst::IConst { dst: v_zero, val: 0 });
        for i in func.param_count as u32..func.locals.len() as u32 {
            c.local_vreg[i as usize] = Some(v_zero);
            c.frame_dirty[i as usize] = true;
        }
    }

    let result_count = func.result_count as usize;
    let ops = &func.body.ops;
    let blocks = &func.body.blocks;

    for (op_idx, op) in ops.iter().enumerate() {
        c.current_op = op_idx as u32;
        let opcode = op.opcode();
        let imm = op.immediate_u32();

        // Accrue fuel cost BEFORE processing the opcode, so that
        // terminators (Return, Trap) can flush then reset pending_fuel
        // without subsequent dead-code fuel leaking through.
        c.accrue_fuel(opcode.fuel_cost());

        match opcode {
            OpCode::Nop => {}

            OpCode::Unreachable => {
                c.emit(IrInst::Trap);
                c.pending_fuel = 0; // dead code after trap
            }

            OpCode::Return => {
                c.flush_fuel_consume_only();
                c.emit_return(result_count);
            }

            OpCode::I32Const => {
                let val = ((imm as i32) << 8 >> 8) as i32;
                c.emit_i32_const(val);
            }

            OpCode::I64Const => {
                let val = ((imm as i32) << 8 >> 8) as i64;
                let dst = c.fresh_vreg();
                c.emit(IrInst::IConst { dst, val });
                c.vpush(dst);
            }

            OpCode::LocalGet => {
                c.emit_local_get(imm);
            }

            OpCode::LocalSet => {
                c.emit_local_set(imm);
            }

            OpCode::LocalTee => {
                let src = c.vpeek();
                // Use local promotion — track in register, defer store.
                c.local_vreg[imm as usize] = Some(src);
                c.frame_dirty[imm as usize] = true;
            }

            OpCode::GlobalGet => {
                let dst = c.fresh_vreg();
                c.emit(IrInst::IConst { dst, val: 0 });
                c.vpush(dst);
            }

            OpCode::GlobalSet => {
                c.vpop();
            }

            OpCode::RefNull => {
                let dst = c.fresh_vreg();
                c.emit(IrInst::IConst { dst, val: 0 });
                c.vpush(dst);
            }

            OpCode::I32Add | OpCode::I32Sub
            | OpCode::I32Mul | OpCode::I32DivS | OpCode::I32DivU
            | OpCode::I32RemS | OpCode::I32RemU
            | OpCode::I32And | OpCode::I32Or | OpCode::I32Xor
            | OpCode::I32Shl | OpCode::I32ShrS | OpCode::I32ShrU
            | OpCode::I32Rotl | OpCode::I32Rotr
            | OpCode::I32Eq | OpCode::I32Ne
            | OpCode::I32LtS | OpCode::I32LtU | OpCode::I32GtS | OpCode::I32GtU
            | OpCode::I32LeS | OpCode::I32LeU | OpCode::I32GeS | OpCode::I32GeU
            | OpCode::I64Add | OpCode::I64Sub | OpCode::I64Mul
            | OpCode::I64DivS | OpCode::I64DivU | OpCode::I64RemS | OpCode::I64RemU
            | OpCode::I64And | OpCode::I64Or | OpCode::I64Xor
            | OpCode::I64Shl | OpCode::I64ShrS | OpCode::I64ShrU
            | OpCode::I64Rotl | OpCode::I64Rotr
            | OpCode::I64Eq | OpCode::I64Ne
            | OpCode::I64LtS | OpCode::I64LtU | OpCode::I64GtS | OpCode::I64GtU
            | OpCode::I64LeS | OpCode::I64LeU | OpCode::I64GeS | OpCode::I64GeU => {
                let alu_op = opcode_to_alu_op(opcode);
                let rhs = c.vpop();
                let lhs = c.vpop();
                let dst = c.fresh_vreg();
                c.emit(IrInst::Alu { op: alu_op, dst, lhs, rhs: Operand::Reg(rhs) });
                c.vpush(dst);
            }

            OpCode::I32Eqz | OpCode::I32Clz | OpCode::I32Ctz | OpCode::I32Popcnt
            | OpCode::I32WrapI64 | OpCode::I32Extend8S | OpCode::I32Extend16S
            | OpCode::I64Clz | OpCode::I64Ctz | OpCode::I64Popcnt
            | OpCode::I64Eqz
            | OpCode::I64ExtendI32S | OpCode::I64ExtendI32U
            | OpCode::I64Extend8S | OpCode::I64Extend16S | OpCode::I64Extend32S => {
                let unary_op = opcode_to_unary_op(opcode);
                let src = c.vpop();
                let dst = c.fresh_vreg();
                c.emit(IrInst::Unary { op: unary_op, dst, src });
                c.vpush(dst);
            }

            OpCode::Drop => {
                c.vpop();
            }

            OpCode::Select => {
                let cond = c.vpop();
                let val2 = c.vpop();
                let val1 = c.vpop();
                let else_label = c.fresh_label();
                let end_label = c.fresh_label();
                let args = c.collect_local_args();
                let slot = c.total_local_count + c.vstack.len() as u32;
                c.emit(IrInst::BrIfZero { cond, label: else_label, args: args.clone() });
                c.emit(IrInst::FrameStore { slot, src: val1 });
                let args2 = c.collect_local_args();
                c.emit(IrInst::Br { label: end_label, args: args2 });
                let params = c.allocate_local_params();
                c.emit(IrInst::DefLabel { label: else_label, params: params.clone() });
                c.apply_local_params(&params);
                c.emit(IrInst::FrameStore { slot, src: val2 });
                let args3 = c.collect_local_args();
                c.emit(IrInst::Br { label: end_label, args: args3 });
                let params2 = c.allocate_local_params();
                c.emit(IrInst::DefLabel { label: end_label, params: params2.clone() });
                c.apply_local_params(&params2);
                let dst = c.fresh_vreg();
                c.emit(IrInst::FrameLoad { dst, slot });
                c.vpush(dst);
            }

            OpCode::Block => {
                let label = c.fresh_label();
                c.block_stack.push(OpenBlock {
                    block_idx: imm,
                    kind: blocks[imm as usize].kind,
                    label,
                    vstack_depth: c.vstack.len(),
                });
            }

            OpCode::Loop => {
                // No fuel flush at loop entry — fuel is checked at
                // back-edges (Br to loop label) and after calls.
                let label = c.fresh_label();
                let args = c.collect_local_args();
                c.emit(IrInst::Br { label, args });
                let params = c.allocate_local_params();
                c.emit(IrInst::DefLabel { label, params: params.clone() });
                c.apply_local_params(&params);
                c.block_stack.push(OpenBlock {
                    block_idx: imm,
                    kind: blocks[imm as usize].kind,
                    label,
                    vstack_depth: c.vstack.len(),
                });
            }

            OpCode::If => {
                let cond_vreg = c.vpop();
                let args = c.collect_local_args();
                let label = c.fresh_label();
                c.emit(IrInst::BrIfZero {
                    cond: cond_vreg,
                    label,
                    args,
                });
                c.block_stack.push(OpenBlock {
                    block_idx: imm,
                    kind: blocks[imm as usize].kind,
                    label,
                    vstack_depth: c.vstack.len(),
                });
            }

            OpCode::Else => {
                let (depth, if_label) = {
                    let block = c.block_stack.last().expect("Else without If");
                    (block.vstack_depth, block.label)
                };
                c.flush_vstack_above(depth);
                let end_label = c.fresh_label();
                let args = c.collect_local_args();
                c.emit(IrInst::Br { label: end_label, args });
                let params = c.allocate_local_params();
                c.emit(IrInst::DefLabel { label: if_label, params: params.clone() });
                c.apply_local_params(&params);
                c.block_stack.last_mut().unwrap().label = end_label;
            }

            OpCode::End => {
                if imm == 0 {
                    c.flush_fuel_consume_only();
                    c.emit_return(result_count);
                } else if let Some(block) = c.block_stack.pop() {
                    if block.kind == BlockKind::If {
                        let branch_results = c.vstack.len() - block.vstack_depth;
                        c.flush_vstack_above(block.vstack_depth);
                        let args = c.collect_local_args();
                        c.emit(IrInst::Br { label: block.label, args });
                        let params = c.allocate_local_params();
                        c.emit(IrInst::DefLabel { label: block.label, params: params.clone() });
                        c.apply_local_params(&params);
                        if branch_results > 0 {
                            c.reload_from_stack(branch_results);
                        }
                    } else {
                        let args = c.collect_local_args();
                        c.emit(IrInst::Br { label: block.label, args });
                        let params = c.allocate_local_params();
                        c.emit(IrInst::DefLabel { label: block.label, params: params.clone() });
                        c.apply_local_params(&params);
                    }
                }
            }

            OpCode::Br => {
                let stack_idx = c
                    .block_stack
                    .iter()
                    .rposition(|b| b.block_idx == imm)
                    .expect("branch target not on block stack");
                if c.block_stack[stack_idx].kind == BlockKind::Loop {
                    c.flush_fuel();
                }
                c.emit_br(imm);
            }

            OpCode::BrIf => {
                let cond_vreg = c.vpop();
                let skip_label = c.fresh_label();
                let args = c.collect_local_args();
                c.emit(IrInst::BrIfZero {
                    cond: cond_vreg,
                    label: skip_label,
                    args: args.clone(),
                });
                let stack_idx = c
                    .block_stack
                    .iter()
                    .rposition(|b| b.block_idx == imm)
                    .expect("branch target not on block stack");
                if c.block_stack[stack_idx].kind == BlockKind::Loop {
                    c.flush_fuel();
                }
                c.emit_br(imm);
                let params = c.allocate_local_params();
                c.emit(IrInst::DefLabel { label: skip_label, params: params.clone() });
                c.apply_local_params(&params);
            }

            OpCode::Call => {
                let callee = &all_funcs[imm as usize];
                let param_count = callee.param_count;
                let has_result = callee.result_count > 0;
                let mut args = Vec::with_capacity(param_count);
                for _ in 0..param_count {
                    args.push(c.vpop());
                }
                args.reverse();
                let spill_count = c.vstack.len();
                c.flush_vstack_above(0);
                c.flush_fuel();
                let result = if has_result {
                    Some(c.fresh_vreg())
                } else {
                    None
                };
                let frame_advance = (2 + c.total_local_count + spill_count as u32) * 8;
                c.emit(IrInst::Call {
                    func_idx: imm,
                    args,
                    result,
                    frame_advance,
                });
                c.invalidate_locals();
                // Reload spilled values back onto vstack.
                if spill_count > 0 {
                    c.reload_from_stack(spill_count);
                }
                if let Some(r) = result {
                    c.vpush(r);
                }
            }

            // --- Superinstructions: decompose into primitive IR ops ---
            OpCode::LocalGetLocalGetAdd => {
                let a_idx = op.imm_u8_a() as u32;
                let b_idx = op.imm_u8_b() as u32;
                c.emit_local_get(a_idx);
                c.emit_local_get(b_idx);
                let rhs = c.vpop();
                let lhs = c.vpop();
                let dst = c.fresh_vreg();
                c.emit(IrInst::Alu { op: AluOp::I32Add, dst, lhs, rhs: Operand::Reg(rhs) });
                c.vpush(dst);
            }

            OpCode::LocalGetI32ConstSub => {
                let local_idx = op.imm_u8_a() as u32;
                let konst = op.imm_i16_hi() as i32;
                c.emit_local_get(local_idx);
                let lhs = c.vpop();
                let dst = c.fresh_vreg();
                if konst >= 0 && konst < 4096 {
                    c.emit(IrInst::Alu { op: AluOp::I32Sub, dst, lhs, rhs: Operand::Imm(konst as i64) });
                } else {
                    c.emit_i32_const(konst);
                    let rhs = c.vpop();
                    c.emit(IrInst::Alu { op: AluOp::I32Sub, dst, lhs, rhs: Operand::Reg(rhs) });
                }
                c.vpush(dst);
            }

            OpCode::LocalGetI32ConstAdd => {
                let local_idx = op.imm_u8_a() as u32;
                let konst = op.imm_i16_hi() as i32;
                c.emit_local_get(local_idx);
                let lhs = c.vpop();
                let dst = c.fresh_vreg();
                if konst >= 0 && konst < 4096 {
                    c.emit(IrInst::Alu { op: AluOp::I32Add, dst, lhs, rhs: Operand::Imm(konst as i64) });
                } else {
                    c.emit_i32_const(konst);
                    let rhs = c.vpop();
                    c.emit(IrInst::Alu { op: AluOp::I32Add, dst, lhs, rhs: Operand::Reg(rhs) });
                }
                c.vpush(dst);
            }

            OpCode::LocalGetReturn => {
                let local_idx = op.imm_u8_a() as u32;
                c.emit_local_get(local_idx);
                c.flush_fuel_consume_only();
                c.emit_return(result_count);
            }

            OpCode::LocalGetI32ConstLeSIf => {
                let local_idx = op.imm_u8_a() as u32;
                let konst = op.imm_u8_b() as i8 as i32;
                let block_idx = op.imm_u8_c() as u32;

                c.emit_local_get(local_idx);
                let lhs = c.vpop();
                // Collect local args before the compare+branch sequence —
                // collect_local_args may emit LocalGet, so placing it before
                // Alu cmp preserves Cmp+BrIfZero fusion.
                let args = c.collect_local_args();
                let cmp_dst = c.fresh_vreg();
                if konst >= 0 && konst < 4096 {
                    c.emit(IrInst::Alu {
                        op: AluOp::I32LeS,
                        dst: cmp_dst,
                        lhs,
                        rhs: Operand::Imm(konst as i64),
                    });
                } else {
                    c.emit_i32_const(konst);
                    let rhs = c.vpop();
                    c.emit(IrInst::Alu {
                        op: AluOp::I32LeS,
                        dst: cmp_dst,
                        lhs,
                        rhs: Operand::Reg(rhs),
                    });
                }

                let label = c.fresh_label();
                c.emit(IrInst::BrIfZero {
                    cond: cmp_dst,
                    label,
                    args,
                });
                c.block_stack.push(OpenBlock {
                    block_idx,
                    kind: blocks[block_idx as usize].kind,
                    label,
                    vstack_depth: c.vstack.len(),
                });
            }

            OpCode::CallLocalSet => {
                let func_idx = op.imm_u16_lo() as u32;
                let local_idx = op.imm_u8_c() as u32;
                let callee = &all_funcs[func_idx as usize];
                let param_count = callee.param_count;
                let has_result = callee.result_count > 0;
                let mut args = Vec::with_capacity(param_count);
                for _ in 0..param_count {
                    args.push(c.vpop());
                }
                args.reverse();
                let spill_count = c.vstack.len();
                c.flush_vstack_above(0);
                c.flush_fuel();
                let result = if has_result {
                    Some(c.fresh_vreg())
                } else {
                    None
                };
                let frame_advance = (2 + c.total_local_count + spill_count as u32) * 8;
                c.emit(IrInst::Call {
                    func_idx,
                    args,
                    result,
                    frame_advance,
                });
                c.invalidate_locals();
                // Reload spilled values back onto vstack.
                if spill_count > 0 {
                    c.reload_from_stack(spill_count);
                }
                if let Some(r) = result {
                    // Use local promotion — track in register, defer store.
                    c.local_vreg[local_idx as usize] = Some(r);
                    c.frame_dirty[local_idx as usize] = true;
                }
            }

            OpCode::LocalGetI32EqzIf => {
                let local_idx = op.imm_u8_a() as u32;
                let block_idx = op.imm_u8_b() as u32;

                c.emit_local_get(local_idx);
                let val = c.vpop();
                let args = c.collect_local_args();

                // eqz(val) is 1 when val==0, 0 when val!=0.
                // BrIfZero on eqz(val) branches when val!=0.
                // Equivalent to BrIfNonZero(val) — lowers to cbnz.
                let label = c.fresh_label();
                c.emit(IrInst::BrIfNonZero {
                    cond: val,
                    label,
                    args,
                });
                c.block_stack.push(OpenBlock {
                    block_idx,
                    kind: blocks[block_idx as usize].kind,
                    label,
                    vstack_depth: c.vstack.len(),
                });
            }

            _ => {
                c.emit(IrInst::Trap);
            }
        }

    }

    let mut ir = IrFunction {
        insts: c.insts,
        source_ops: c.source_ops,
        param_count: func.param_count as u32,
        total_local_count: func.locals.len() as u32,
        max_operand_depth: c.max_vstack_depth as u32,
        result_count: func.result_count,
    };

    eliminate_dead_load_store_pairs(&mut ir);

    ir
}

/// Remove redundant FrameLoad+FrameStore pairs where a value is loaded
/// from a slot and immediately stored back to the same slot.
///
/// This pattern arises at call boundaries: `flush_vstack_above` spills
/// values, `reload_from_stack` reloads them, and a subsequent flush
/// stores them right back. The reload+re-store is a no-op.
fn eliminate_dead_load_store_pairs(ir: &mut IrFunction) {
    let len = ir.insts.len();
    if len < 2 {
        return;
    }

    let mut remove = vec![false; len];

    for i in 0..len - 1 {
        if let (
            IrInst::FrameLoad { dst, slot: load_slot },
            IrInst::FrameStore { slot: store_slot, src },
        ) = (&ir.insts[i], &ir.insts[i + 1])
        {
            if load_slot == store_slot && dst == src {
                remove[i] = true;
                remove[i + 1] = true;
            }
        }
    }

    if remove.iter().any(|&r| r) {
        let mut new_insts = Vec::with_capacity(len);
        let mut new_source_ops = Vec::with_capacity(len);
        for i in 0..len {
            if !remove[i] {
                new_insts.push(ir.insts[i].clone());
                new_source_ops.push(ir.source_ops[i]);
            }
        }
        ir.insts = new_insts;
        ir.source_ops = new_source_ops;
    }
}

fn opcode_to_alu_op(op: OpCode) -> AluOp {
    match op {
        OpCode::I32Add => AluOp::I32Add, OpCode::I32Sub => AluOp::I32Sub,
        OpCode::I32Mul => AluOp::I32Mul, OpCode::I32DivS => AluOp::I32DivS,
        OpCode::I32DivU => AluOp::I32DivU, OpCode::I32RemS => AluOp::I32RemS,
        OpCode::I32RemU => AluOp::I32RemU,
        OpCode::I32And => AluOp::I32And, OpCode::I32Or => AluOp::I32Or,
        OpCode::I32Xor => AluOp::I32Xor, OpCode::I32Shl => AluOp::I32Shl,
        OpCode::I32ShrS => AluOp::I32ShrS, OpCode::I32ShrU => AluOp::I32ShrU,
        OpCode::I32Rotl => AluOp::I32Rotl, OpCode::I32Rotr => AluOp::I32Rotr,
        OpCode::I32Eq => AluOp::I32Eq, OpCode::I32Ne => AluOp::I32Ne,
        OpCode::I32LtS => AluOp::I32LtS, OpCode::I32LtU => AluOp::I32LtU,
        OpCode::I32GtS => AluOp::I32GtS, OpCode::I32GtU => AluOp::I32GtU,
        OpCode::I32LeS => AluOp::I32LeS, OpCode::I32LeU => AluOp::I32LeU,
        OpCode::I32GeS => AluOp::I32GeS, OpCode::I32GeU => AluOp::I32GeU,
        OpCode::I64Add => AluOp::I64Add, OpCode::I64Sub => AluOp::I64Sub,
        OpCode::I64Mul => AluOp::I64Mul, OpCode::I64DivS => AluOp::I64DivS,
        OpCode::I64DivU => AluOp::I64DivU, OpCode::I64RemS => AluOp::I64RemS,
        OpCode::I64RemU => AluOp::I64RemU,
        OpCode::I64And => AluOp::I64And, OpCode::I64Or => AluOp::I64Or,
        OpCode::I64Xor => AluOp::I64Xor, OpCode::I64Shl => AluOp::I64Shl,
        OpCode::I64ShrS => AluOp::I64ShrS, OpCode::I64ShrU => AluOp::I64ShrU,
        OpCode::I64Rotl => AluOp::I64Rotl, OpCode::I64Rotr => AluOp::I64Rotr,
        OpCode::I64Eq => AluOp::I64Eq, OpCode::I64Ne => AluOp::I64Ne,
        OpCode::I64LtS => AluOp::I64LtS, OpCode::I64LtU => AluOp::I64LtU,
        OpCode::I64GtS => AluOp::I64GtS, OpCode::I64GtU => AluOp::I64GtU,
        OpCode::I64LeS => AluOp::I64LeS, OpCode::I64LeU => AluOp::I64LeU,
        OpCode::I64GeS => AluOp::I64GeS, OpCode::I64GeU => AluOp::I64GeU,
        _ => unreachable!("not a binary alu opcode: {op:?}"),
    }
}

fn opcode_to_unary_op(op: OpCode) -> UnaryOp {
    match op {
        OpCode::I32Clz => UnaryOp::I32Clz, OpCode::I32Ctz => UnaryOp::I32Ctz,
        OpCode::I32Popcnt => UnaryOp::I32Popcnt, OpCode::I32Eqz => UnaryOp::I32Eqz,
        OpCode::I64Clz => UnaryOp::I64Clz, OpCode::I64Ctz => UnaryOp::I64Ctz,
        OpCode::I64Popcnt => UnaryOp::I64Popcnt, OpCode::I64Eqz => UnaryOp::I64Eqz,
        OpCode::I32WrapI64 => UnaryOp::I32WrapI64,
        OpCode::I64ExtendI32S => UnaryOp::I64ExtendI32S,
        OpCode::I64ExtendI32U => UnaryOp::I64ExtendI32U,
        OpCode::I32Extend8S => UnaryOp::I32Extend8S,
        OpCode::I32Extend16S => UnaryOp::I32Extend16S,
        OpCode::I64Extend8S => UnaryOp::I64Extend8S,
        OpCode::I64Extend16S => UnaryOp::I64Extend16S,
        OpCode::I64Extend32S => UnaryOp::I64Extend32S,
        _ => unreachable!("not a unary opcode: {op:?}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Compile a parsed wasm function into IR with fuel checks.
    pub(crate) fn compile(func: &ParsedFunction, all_funcs: &[ParsedFunction]) -> IrFunction {
        compile_with(func, all_funcs, true)
    }

    /// Parse WAT, compile the first function to IR.
    fn compile_wat_ir(wat: &str) -> IrFunction {
        let wasm_bytes = wat::parse_str(wat).expect("failed to parse WAT");
        let engine = crate::Engine::default();
        let module =
            crate::Module::from_bytes(&engine, &wasm_bytes).expect("failed to parse module");
        compile(&module.funcs[0], &module.funcs)
    }

    #[test]
    fn ir_ackermann() {
        let ir = compile_wat_ir(
            r#"(module
                (func $ack (export "ack") (param $m i32) (param $n i32) (result i32)
                  (if (result i32) (i32.eqz (local.get $m))
                    (then
                      (i32.add (local.get $n) (i32.const 1))
                    )
                    (else
                      (if (result i32) (i32.eqz (local.get $n))
                        (then
                          (call $ack (i32.sub (local.get $m) (i32.const 1)) (i32.const 1))
                        )
                        (else
                          (call $ack
                            (i32.sub (local.get $m) (i32.const 1))
                            (call $ack (local.get $m) (i32.sub (local.get $n) (i32.const 1)))
                          )
                        )
                      )
                    )
                  )
                )
              )"#,
        );
        eprintln!("{ir}");
    }

    #[test]
    fn ir_identity() {
        let ir = compile_wat_ir(r#"(module (func (param i32) (result i32) (local.get 0)))"#);
        let text = format!("{ir}");
        eprintln!("{text}");
        assert!(text.contains("param 0"));
        assert!(text.contains("return"));
    }

    #[test]
    fn ir_add() {
        let ir = compile_wat_ir(
            r#"(module (func (param i32 i32) (result i32)
                (i32.add (local.get 0) (local.get 1))))"#,
        );
        let text = format!("{ir}");
        eprintln!("{text}");
        assert!(text.contains("i32.add"));
    }

    #[test]
    fn ir_recursive_fib() {
        let ir = compile_wat_ir(
            r#"(module
                (func $fib (param i32) (result i32)
                    (if (result i32) (i32.le_s (local.get 0) (i32.const 1))
                        (then (local.get 0))
                        (else
                            (i32.add
                                (call $fib (i32.sub (local.get 0) (i32.const 1)))
                                (call $fib (i32.sub (local.get 0) (i32.const 2)))
                            )
                        )
                    )
                )
            )"#,
        );
        let text = format!("{ir}");
        eprintln!("{text}");
        assert!(text.contains("call"));
        assert!(text.contains("i32.sub"));
        assert!(text.contains("i32.le_s"));
    }
}
