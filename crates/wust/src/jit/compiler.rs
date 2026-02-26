use wust_codegen::ir::{IrCond, IrFunction, IrInst, Label, VReg};
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
}

impl IrCompiler {
    fn new(total_local_count: u32) -> Self {
        IrCompiler {
            insts: Vec::new(),
            vstack: Vec::new(),
            next_vreg: 0,
            next_label: 0,
            block_stack: Vec::new(),
            max_vstack_depth: 0,
            total_local_count,
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
        let dst = self.fresh_vreg();
        self.emit(IrInst::LocalGet { dst, idx });
        self.vpush(dst);
    }

    fn emit_local_set(&mut self, idx: u32) {
        let src = self.vpop();
        self.emit(IrInst::LocalSet { idx, src });
    }

    fn emit_return(&mut self, result_count: usize) {
        let mut results = Vec::with_capacity(result_count);
        for _ in 0..result_count {
            results.push(self.vpop());
        }
        results.reverse();
        self.emit(IrInst::Return { results });
    }

    fn emit_br(&mut self, block_idx: u32) {
        let stack_idx = self
            .block_stack
            .iter()
            .rposition(|b| b.block_idx == block_idx)
            .expect("branch target not on block stack");
        let label = self.block_stack[stack_idx].label;
        self.emit(IrInst::Br { label });
    }

    /// Flush only the values above `depth` from the virtual stack.
    ///
    /// Used at if/else merge points: stores branch results to frame
    /// operand stack slots, then truncates vstack to the given depth.
    fn flush_vstack_above(&mut self, depth: usize) {
        let base = self.total_local_count;
        let extras: Vec<VReg> = self.vstack.drain(depth..).collect();
        for (i, vreg) in extras.into_iter().enumerate() {
            self.insts.push(IrInst::FrameStore {
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
            self.insts.push(IrInst::FrameLoad {
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
/// Each wasm opcode emits a group of IR instructions, followed by a
/// single `FuelCheck` (when `emit_fuel` is true). This keeps fused
/// operations (e.g. Cmp+BrIfZero from i32.eqz+if) adjacent — the
/// fuel check always comes after the whole group.
pub(crate) fn compile_with(
    func: &ParsedFunction,
    all_funcs: &[ParsedFunction],
    emit_fuel: bool,
) -> IrFunction {
    let mut c = IrCompiler::new(func.locals.len() as u32);

    let result_count = func.result_count as usize;
    let ops = &func.body.ops;
    let blocks = &func.body.blocks;

    for op in ops.iter() {
        let opcode = op.opcode();
        let imm = op.immediate_u32();

        match opcode {
            OpCode::Nop => {}

            OpCode::Unreachable => {
                c.emit(IrInst::Trap);
            }

            OpCode::Return => {
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
                c.emit(IrInst::LocalSet { idx: imm, src });
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

            OpCode::I32Add => {
                let rhs = c.vpop();
                let lhs = c.vpop();
                let dst = c.fresh_vreg();
                c.emit(IrInst::Add { dst, lhs, rhs });
                c.vpush(dst);
            }

            OpCode::I32Sub => {
                let rhs = c.vpop();
                let lhs = c.vpop();
                let dst = c.fresh_vreg();
                c.emit(IrInst::Sub { dst, lhs, rhs });
                c.vpush(dst);
            }

            OpCode::I32Eqz => {
                let val = c.vpop();
                let zero = c.fresh_vreg();
                c.emit(IrInst::IConst { dst: zero, val: 0 });
                let dst = c.fresh_vreg();
                c.emit(IrInst::Cmp {
                    dst,
                    lhs: val,
                    rhs: zero,
                    cond: IrCond::Eq,
                });
                c.vpush(dst);
            }

            OpCode::I32LeS => {
                let rhs = c.vpop();
                let lhs = c.vpop();
                let dst = c.fresh_vreg();
                c.emit(IrInst::Cmp {
                    dst,
                    lhs,
                    rhs,
                    cond: IrCond::LeS,
                });
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
                let label = c.fresh_label();
                c.emit(IrInst::DefLabel { label });
                c.block_stack.push(OpenBlock {
                    block_idx: imm,
                    kind: blocks[imm as usize].kind,
                    label,
                    vstack_depth: c.vstack.len(),
                });
            }

            OpCode::If => {
                let cond_vreg = c.vpop();
                let label = c.fresh_label();
                c.emit(IrInst::BrIfZero {
                    cond: cond_vreg,
                    label,
                });
                // Flush AFTER BrIfZero so Cmp+BrIfZero stay adjacent
                // for fusion in the lowerer.
                c.block_stack.push(OpenBlock {
                    block_idx: imm,
                    kind: blocks[imm as usize].kind,
                    label,
                    vstack_depth: c.vstack.len(),
                });
            }

            OpCode::Else => {
                // At Else, the then-branch has produced values on the
                // vstack. Flush them to the physical wasm stack so the
                // merge point (End) can reload them uniformly.
                let (depth, if_label) = {
                    let block = c.block_stack.last().expect("Else without If");
                    (block.vstack_depth, block.label)
                };
                c.flush_vstack_above(depth);
                let end_label = c.fresh_label();
                c.emit(IrInst::Br { label: end_label });
                c.insts.push(IrInst::DefLabel { label: if_label });
                c.block_stack.last_mut().unwrap().label = end_label;
            }

            OpCode::End => {
                if imm == 0 {
                    c.emit_return(result_count);
                } else if let Some(block) = c.block_stack.pop() {
                    if block.kind == BlockKind::If {
                        // At End of if/else block: else-branch values are
                        // on the vstack. Flush them, define the merge label,
                        // then reload results from the physical stack.
                        let branch_results = c.vstack.len() - block.vstack_depth;
                        c.flush_vstack_above(block.vstack_depth);
                        c.emit(IrInst::DefLabel { label: block.label });
                        if branch_results > 0 {
                            c.reload_from_stack(branch_results);
                        }
                    } else {
                        c.emit(IrInst::DefLabel { label: block.label });
                    }
                }
            }

            OpCode::Br => {
                c.emit_br(imm);
            }

            OpCode::BrIf => {
                let cond_vreg = c.vpop();
                let skip_label = c.fresh_label();
                c.emit(IrInst::BrIfZero {
                    cond: cond_vreg,
                    label: skip_label,
                });
                c.emit_br(imm);
                c.emit(IrInst::DefLabel { label: skip_label });
            }

            OpCode::Call => {
                let callee = &all_funcs[imm as usize];
                let param_count = callee.param_count;
                let has_result = callee.result_count > 0;
                // Pop args from vstack (in reverse, then reverse back).
                let mut args = Vec::with_capacity(param_count);
                for _ in 0..param_count {
                    args.push(c.vpop());
                }
                args.reverse();
                // Spill any remaining vstack values to frame slots so they
                // survive the call (scratch registers are clobbered).
                let spill_count = c.vstack.len();
                c.flush_vstack_above(0);
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
                c.emit(IrInst::Add { dst, lhs, rhs });
                c.vpush(dst);
            }

            OpCode::LocalGetI32ConstSub => {
                let local_idx = op.imm_u8_a() as u32;
                let konst = op.imm_i16_hi() as i32;
                c.emit_local_get(local_idx);
                c.emit_i32_const(konst);
                let rhs = c.vpop();
                let lhs = c.vpop();
                let dst = c.fresh_vreg();
                c.emit(IrInst::Sub { dst, lhs, rhs });
                c.vpush(dst);
            }

            OpCode::LocalGetI32ConstAdd => {
                let local_idx = op.imm_u8_a() as u32;
                let konst = op.imm_i16_hi() as i32;
                c.emit_local_get(local_idx);
                c.emit_i32_const(konst);
                let rhs = c.vpop();
                let lhs = c.vpop();
                let dst = c.fresh_vreg();
                c.emit(IrInst::Add { dst, lhs, rhs });
                c.vpush(dst);
            }

            OpCode::LocalGetReturn => {
                let local_idx = op.imm_u8_a() as u32;
                c.emit_local_get(local_idx);
                c.emit_return(result_count);
            }

            OpCode::LocalGetI32ConstLeSIf => {
                let local_idx = op.imm_u8_a() as u32;
                let konst = op.imm_u8_b() as i8 as i32;
                let block_idx = op.imm_u8_c() as u32;

                c.emit_local_get(local_idx);
                c.emit_i32_const(konst);
                let rhs = c.vpop();
                let lhs = c.vpop();
                let cmp_dst = c.fresh_vreg();
                c.emit(IrInst::Cmp {
                    dst: cmp_dst,
                    lhs,
                    rhs,
                    cond: IrCond::LeS,
                });

                let label = c.fresh_label();
                c.emit(IrInst::BrIfZero {
                    cond: cmp_dst,
                    label,
                });
                // Flush AFTER BrIfZero so Cmp+BrIfZero stay adjacent.
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
                // Spill remaining vstack values across the call.
                let spill_count = c.vstack.len();
                c.flush_vstack_above(0);
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
                // Reload spilled values back onto vstack.
                if spill_count > 0 {
                    c.reload_from_stack(spill_count);
                }
                if let Some(r) = result {
                    c.emit(IrInst::LocalSet {
                        idx: local_idx,
                        src: r,
                    });
                }
            }

            OpCode::LocalGetI32EqzIf => {
                let local_idx = op.imm_u8_a() as u32;
                let block_idx = op.imm_u8_b() as u32;

                c.emit_local_get(local_idx);
                let val = c.vpop();
                let zero = c.fresh_vreg();
                c.emit(IrInst::IConst { dst: zero, val: 0 });
                let cmp_dst = c.fresh_vreg();
                c.emit(IrInst::Cmp {
                    dst: cmp_dst,
                    lhs: val,
                    rhs: zero,
                    cond: IrCond::Eq,
                });

                let label = c.fresh_label();
                c.emit(IrInst::BrIfZero {
                    cond: cmp_dst,
                    label,
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

        if emit_fuel {
            let cost = opcode.fuel_cost();
            if cost > 0 {
                c.emit(IrInst::FuelCheck { cost });
            }
        }
    }

    IrFunction {
        insts: c.insts,
        param_count: func.param_count as u32,
        total_local_count: func.locals.len() as u32,
        max_operand_depth: c.max_vstack_depth as u32,
        result_count: func.result_count,
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
        assert!(text.contains("local.get 0"));
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
