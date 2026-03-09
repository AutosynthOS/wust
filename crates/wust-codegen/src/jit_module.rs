use std::marker::PhantomData;

use autosynth_backend::BackendEmitter;
use autosynth_codegen::{
    AluOp, BlockId, CodeBuilder, CompOp, FunctionBuilder, FunctionIdx, IrInst, Operand, Register,
    VStack, Width,
};
use autosynth_isa::{IsaReg, PReg};
use autosynth_orchestrator::Orchestrator;

use wust_core::exec::ModuleExecutor;
use wust_core::{FRAME_HEADER_SIZE, FuncMeta, OpCode, Outcome, ParsedModule, Task};

use crate::conversion::{build_signatures, func_signature, valtype_to_width};
use crate::trampoline::{call_trampoline, emit_entry_trampoline};
use crate::CodeBuffer;

/// A JIT-compiled WASM module, generic over the backend.
///
/// Owns the parsed module, the autosynth IR compiler state, and an
/// executable code page. Constructs the orchestrator internally from
/// the backend's machine config.
pub struct JitModule<B: BackendEmitter> {
    _module: ParsedModule,
    compiler: CodeBuilder,
    page: CodeBuffer,
    /// Byte offset of each function's entry trampoline within the code page.
    trampoline_offsets: Vec<usize>,
    _backend: PhantomData<B>,
}

impl<B: BackendEmitter> JitModule<B> {
    /// Compile all functions in the parsed WASM module to native code.
    pub fn new(module: ParsedModule) -> Result<Self, anyhow::Error> {
        let (mut backend, mut config) = B::new();
        config.reserve("lbp", IsaReg::FramePointer);
        config.reserve("lr", IsaReg::ReturnAddress);
        config.reserve("fsp", IsaReg::StackPointer);
        config.reserve("fuel", IsaReg::Alloc64(-1));
        config.reserve("ctx", IsaReg::Alloc64(-2));

        let mut orch = Orchestrator::new(config);
        let mut compiler = CodeBuilder::new();

        let signatures = build_signatures(&module);
        for (idx, sig) in signatures {
            compiler.add_signature(idx, sig);
        }

        let mut page = CodeBuffer::new()?;
        let mut all_code: Vec<u8> = Vec::new();
        let mut trampoline_offsets: Vec<usize> = Vec::new();

        for (func_idx, func) in module.funcs.iter().enumerate() {
            Self::compile_func(&mut compiler, orch.config(), func_idx as i32, &module.funcs)?;

            let ir_func = &compiler.functions()[compiler.functions().len() - 1];
            let body_bytes = orch
                .compile(ir_func, &mut backend)
                .map_err(|e| anyhow::anyhow!(e))?;

            let trampoline_bytes = emit_entry_trampoline(func);

            let trampoline_offset = all_code.len();
            trampoline_offsets.push(trampoline_offset);
            all_code.extend_from_slice(&trampoline_bytes);
            all_code.extend_from_slice(&body_bytes);
        }

        page.flash(&all_code)?;

        Ok(JitModule {
            _module: module,
            compiler,
            page,
            trampoline_offsets,
            _backend: PhantomData,
        })
    }

    /// Access the compiled IR (for debugging/inspection).
    pub fn ir(&self) -> &CodeBuilder {
        &self.compiler
    }

    /// Compile a single WASM function into autosynth IR.
    ///
    /// If a debugger is installed via [`autosynth_codegen::debugger::install`],
    /// source-level annotations are recorded automatically.
    pub fn compile_func(
        cb: &mut CodeBuilder,
        config: &autosynth_backend::MachineConfig,
        func_idx: i32,
        all_funcs: &[FuncMeta],
    ) -> anyhow::Result<()> {
        let func = &all_funcs[func_idx as usize];
        let sig = func_signature(func);

        let mut f = FunctionBuilder::new(cb, sig);

        let lbp = config.use_reserved("lbp");
        let lr = config.use_reserved("lr");
        let fuel = config.use_reserved("fuel");
        let _ctx = config.use_reserved("ctx");
        let fsp = config.use_reserved("fsp");

        // Entry block must be active before defining vstacks,
        // since vstack state lives on the block.
        f.entry_block(BlockId::Entry);

        // Virtual stacks anchored to physical registers
        //
        // [param0, param1, local_2, ...][frame header][operands]
        // ^ lbp
        let locals = f.define_vstack(VStack {
            label: "local",
            base: lbp,
            offset: 0,
        });
        let operands = f.define_vstack(VStack {
            label: "ops",
            base: lbp,
            offset: func.locals_size as u32 + FRAME_HEADER_SIZE as u32,
        });
        let fibre = f.define_vstack(VStack {
            label: "fibre",
            base: fsp,
            offset: 0,
        });

        // "operation" column registered after all vstacks so it appears rightmost.
        f.finish_entry();

        // Declare parameters — each starts in its CC register (PReg(i)).
        f.begin_op("--", "params_start");
        for (i, param) in func.params.iter().enumerate() {
            let w = valtype_to_width(param);
            f.define_slot(locals, i, w, Some(Operand::PReg(PReg(i as u8), w)));
        }

        f.begin_op("--", "locals_start");
        // Declare zero-initialized locals
        for (i, local) in func.locals.iter().enumerate() {
            f.define_slot(
                locals,
                i + func.params.len(),
                valtype_to_width(&local),
                Some(Operand::ConstI64(0)),
            );
        }

        f.begin_op("--", "prologue");

        // Finalize entry block, branch to first user block.
        f.br(BlockId::User(0));
        f.start_block(BlockId::User(0));

        // Fuel tracking: accumulate cost per opcode, flush before calls.
        let mut pending_fuel: u32 = 0;
        // LR is saved lazily — only before the first call instruction.
        let mut lr_saved = false;
        let locals_header_size = func.locals_size as u32 + FRAME_HEADER_SIZE as u32;
        let fsp_preg = match fsp { Register::PReg(p, _) => p, _ => unreachable!() };

        // Main compilation loop
        let mut pc = 0;
        loop {
            debug_assert!(
                pc < func.body.ops.len(),
                "pc {pc} out of bounds (len={})",
                func.body.ops.len()
            );
            let inline_op = unsafe { func.body.ops.get_unchecked(pc) };
            let op = inline_op.opcode();

            f.begin_op(&pc.to_string(), &inline_op.display_label());

            // Accrue fuel cost for this opcode.
            pending_fuel += op.fuel_cost();

            match op {
                OpCode::I32Const => {
                    f.push(
                        operands,
                        Width::W32,
                        Some(Operand::ConstI32(inline_op.immediate_i32())),
                    );
                }

                OpCode::LocalGetI32 => {
                    let idx = inline_op.local_index();
                    let src = f.get_slot(locals, idx as usize);
                    f.push(operands, Width::W32, Some(Operand::VReg(src, Width::W32)));
                }
                OpCode::LocalSetI32 => {
                    let idx = inline_op.local_index();
                    let val = f.pop(operands, Width::W32);
                    f.define_slot(locals, idx as usize, Width::W32, Some(Operand::VReg(val, Width::W32)));
                }

                OpCode::I32Add => {
                    let rhs = f.pop(operands, Width::W32);
                    let lhs = f.pop(operands, Width::W32);
                    let dst = f.push_dst(operands, Width::W32);
                    f.emit(IrInst::Alu {
                        op: AluOp::Add,
                        dst: Register::VReg(dst, Width::W32),
                        lhs: Operand::VReg(lhs, Width::W32),
                        rhs: Operand::VReg(rhs, Width::W32),
                    });
                }
                OpCode::I32Sub => {
                    let rhs = f.pop(operands, Width::W32);
                    let lhs = f.pop(operands, Width::W32);
                    let dst = f.push_dst(operands, Width::W32);
                    f.emit(IrInst::Alu {
                        op: AluOp::Sub,
                        dst: Register::VReg(dst, Width::W32),
                        lhs: Operand::VReg(lhs, Width::W32),
                        rhs: Operand::VReg(rhs, Width::W32),
                    });
                }

                OpCode::I32LeS => {
                    let rhs = f.pop(operands, Width::W32);
                    let lhs = f.pop(operands, Width::W32);
                    let dst = f.push_dst(operands, Width::W32);
                    f.emit(IrInst::Alu {
                        op: AluOp::Comp(CompOp::LeS),
                        dst: Register::VReg(dst, Width::W32),
                        lhs: Operand::VReg(lhs, Width::W32),
                        rhs: Operand::VReg(rhs, Width::W32),
                    });
                }

                OpCode::If => {
                    let block_idx = inline_op.immediate_u32();
                    let cond = f.pop(operands, Width::W32);
                    let then_block = BlockId::User(pc as u32 + 1);
                    let end_pc = func.body.blocks[block_idx as usize].end_pc;
                    let cont_block = BlockId::User(end_pc);
                    f.br_if(cond, then_block, cont_block);
                    f.start_block(then_block);
                }
                OpCode::BrIf => {
                    let block_idx = inline_op.immediate_u32();
                    let target_block = &func.body.blocks[block_idx as usize];
                    let target = BlockId::User(target_block.end_pc);
                    let cont = BlockId::User(pc as u32 + 1);
                    let cond = f.pop(operands, Width::W32);
                    f.br_if(cond, target, cont);
                    f.start_block(cont);
                }
                OpCode::End => {
                    let block_idx = inline_op.immediate_u32();
                    if block_idx == 0 {
                        if lr_saved {
                            // ldr lr, [fsp, #0]
                            f.emit(IrInst::Load {
                                dst: lr,
                                base: fsp_preg,
                                offset: 0,
                            });
                            // add fsp, fsp, #16
                            f.emit(IrInst::Alu {
                                op: AluOp::Add,
                                dst: fsp,
                                lhs: Operand::from(fsp),
                                rhs: Operand::ConstI32(16),
                            });
                        }
                        f.emit_return(operands);
                        break;
                    }
                    // Wasm block end — finalize current block if not already done.
                    if !f.is_finalized() {
                        f.br(BlockId::User(pc as u32));
                    }
                    f.start_block(BlockId::User(pc as u32));
                }

                OpCode::Return => {
                    if lr_saved {
                        // ldr lr, [fsp, #0]
                        f.emit(IrInst::Load {
                            dst: lr,
                            base: fsp_preg,
                            offset: 0,
                        });
                        // add fsp, fsp, #16
                        f.emit(IrInst::Alu {
                            op: AluOp::Add,
                            dst: fsp,
                            lhs: Operand::from(fsp),
                            rhs: Operand::ConstI32(16),
                        });
                    }
                    f.emit_return(operands);
                }

                OpCode::Call => {
                    let callee_idx = inline_op.immediate_i32();
                    if callee_idx.is_negative() {
                        todo!("call to negative index function");
                    }

                    // Save LR to fibre stack (once, before first call).
                    if !lr_saved {
                        lr_saved = true;
                        // sub fsp, fsp, #16
                        f.emit(IrInst::Alu {
                            op: AluOp::Sub,
                            dst: fsp,
                            lhs: Operand::from(fsp),
                            rhs: Operand::ConstI32(16),
                        });
                        // str lr, [fsp, #0]
                        f.emit(IrInst::Store {
                            src: Operand::from(lr),
                            base: fsp_preg,
                            offset: 0,
                        });
                    }

                    // Frame advance: add lbp, lbp, #locals_header_size
                    f.emit(IrInst::Alu {
                        op: AluOp::Add,
                        dst: lbp,
                        lhs: Operand::from(lbp),
                        rhs: Operand::ConstI32(locals_header_size as i32),
                    });

                    let func_idx = FunctionIdx::User(callee_idx as u32);
                    f.emit_call(operands, func_idx);

                    // Frame restore: sub lbp, lbp, #locals_header_size
                    f.emit(IrInst::Alu {
                        op: AluOp::Sub,
                        dst: lbp,
                        lhs: Operand::from(lbp),
                        rhs: Operand::ConstI32(locals_header_size as i32),
                    });

                    // Fused subtract-and-compare: subs fuel, fuel, #N
                    // LeS makes the backend emit `subs` (flag-setting subtract).
                    // Using `fuel` (physical register) as dst writes the result
                    // back to fuel while setting flags for the LE condition.
                    let fuel_cond = f.alloc_temp(Width::W32, Some(Operand::ConstI64(0)));
                    f.emit(IrInst::Alu {
                        op: AluOp::Comp(CompOp::LeS),
                        dst: fuel,
                        lhs: Operand::from(fuel),
                        rhs: Operand::ConstI32(pending_fuel as i32),
                    });
                    pending_fuel = 0;

                    let suspend_block = f.gen_block();
                    let cont_block = BlockId::User(pc as u32);

                    f.br_if(fuel_cond, suspend_block, cont_block);

                    f.start_block(suspend_block);
                    f.ret();

                    f.start_block(cont_block);
                }

                _ => todo!("unhandled opcode: {:?}", op),
            }

            pc += 1;
        }

        f.build();
        Ok(())
    }
}

impl<B: BackendEmitter> ModuleExecutor for JitModule<B> {
    /// Execute JIT-compiled code for the current task.
    ///
    /// Sets up registers for the JIT calling convention, calls
    /// the entry trampoline via inline asm, and stores results
    /// back to the task context.
    fn poll(&self, task: &mut Task) -> Outcome {
        let func_idx = *task.context.wasm_fp.frame().func_idx as usize;
        let trampoline_offset = self.trampoline_offsets[func_idx];
        let trampoline_ptr = unsafe { self.page.entry().add(trampoline_offset) };

        call_trampoline(trampoline_ptr, &mut task.context)
    }
}
