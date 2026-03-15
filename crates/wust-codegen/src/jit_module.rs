use std::marker::PhantomData;

use autosynth_codegen::{
    Align, AluOp, BlockId, CodeBuilder, CompOp, FunctionBuilder, FunctionIdx, IrInst, RegInst,
    VInit, VReg, VRegion, VRegionId, Width, debugger,
};
use autosynth_isa::{IsaReg, PReg};
use autosynth_lower::{BackendEmitter, MachineConfig};

use wust_core::exec::ModuleExecutor;
use wust_core::{FRAME_HEADER_SIZE, FuncMeta, OpCode, Outcome, ParsedModule, Task, slot_size};

use crate::CodeBuffer;
use crate::conversion::{build_signatures, func_signature, valtype_to_width};
use crate::trampoline::{call_trampoline, emit_entry_trampoline};

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
        let mut backend = B::new();
        let mut compiler = CodeBuilder::new();

        let signatures = build_signatures(&module);
        for (idx, sig) in signatures {
            compiler.add_signature(idx, sig);
        }

        let mut page = CodeBuffer::new()?;
        let mut all_code: Vec<u8> = Vec::new();
        let mut trampoline_offsets: Vec<usize> = Vec::new();

        for (func_idx, func) in module.funcs.iter().enumerate() {
            Self::compile_func(
                &mut compiler,
                B::machine_config(),
                func_idx as i32,
                &module.funcs,
            )?;

            let ir_func = &compiler.functions()[compiler.functions().len() - 1];
            let body_bytes = autosynth_codegen::compile(ir_func, &mut backend)
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
        mut config: MachineConfig,
        func_idx: i32,
        all_funcs: &[FuncMeta],
    ) -> anyhow::Result<()> {
        let func = &all_funcs[func_idx as usize];
        let sig = func_signature(func);

        let lbp_preg = config.reserve(IsaReg::FramePointer);
        let lr_preg = config.reserve(IsaReg::ReturnAddress);
        let fuel_preg = config.reserve(IsaReg::FromEnd);
        let _ctx_preg = config.reserve(IsaReg::FromEnd);
        let fsp_preg = config.reserve(IsaReg::StackPointer);
        let stack_alignment = config.stack_alignment();

        let mut f = FunctionBuilder::new(cb, config, sig);

        // Entry block must be active before defining vstacks,
        // since vstack state lives on the block.
        f.entry_block(BlockId::Entry);

        // g.lb (locals-base) points to the start of the frame. All stack
        // access uses positive unsigned offsets from g.lb, which gives
        // 0–16KB range via ARM64's ldr/str [Xn, #imm12] encoding.
        // See abi.md "JIT locals-base register" for the full rationale.
        //
        // [params][locals][FrameHeader 12B][operands...]
        // ^g.lb           ^+locals_size    ^+locals_header_size
        let locals_header_size = func.locals_size as u32 + FRAME_HEADER_SIZE as u32;

        let locals = f.define_region(VRegion {
            label: "local",
            base: lbp_preg,
            base_offset: 0,
            slots: Vec::new(),
        });
        let operands = f.define_region(VRegion {
            label: "ops",
            base: lbp_preg,
            base_offset: locals_header_size,
            slots: Vec::new(),
        });
        let fibre = f.define_region(VRegion {
            label: "fibre",
            base: fsp_preg,
            base_offset: 0,
            slots: Vec::new(),
        });

        // "operation" column registered after all vstacks so it appears rightmost.
        debugger::dbg(|dbg| dbg.add_source_column("operation", Align::Left));

        // Declare parameters — each starts in its CC register (PReg(i)).
        for (i, param) in func.params.iter().enumerate() {
            f.begin_op(&format!("p{i}"), &format!("param {i} = {param}"));
            let w = valtype_to_width(param);
            let preg = PReg(i as u8);
            let v = f.alloc_vreg(w, VInit::PReg(preg));
            f.push_vreg(locals, v);
        }

        // Declare zero-initialized locals
        for (i, local) in func.locals.iter().enumerate() {
            let idx = i + func.params.len();
            f.begin_op(&format!("l{idx}"), &format!("local {idx} = {local}"));
            let w = valtype_to_width(&local);
            let v = f.alloc_vreg(w, VInit::Const(0));
            f.push_vreg(locals, v);
        }

        // Allocate native stack space for the fibre (lr save slot).
        let sp = f.alloc_vreg(Width::W64, VInit::PReg(fsp_preg));
        let frame_size = f.alloc_vreg(Width::W64, VInit::Const(stack_alignment as i64));
        f.emit(IrInst::Alu {
            op: AluOp::Sub,
            dst: sp,
            lhs: sp,
            rhs: frame_size,
        });

        // Save link register onto fibre.
        let lr = f.alloc_vreg(Width::W64, VInit::PReg(lr_preg));
        f.push_vreg(fibre, lr);

        f.begin_op("--", "prologue");

        // Finalize entry block, branch to first user block.
        f.br(BlockId::User(0));
        f.start_block(BlockId::User(0));
        f.begin_op("--", "body");

        // Fuel tracking: accumulate cost per opcode, flush before calls.
        let mut pending_fuel: u32 = 0;

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
                    let value = inline_op.immediate_i32() as i64;
                    let v = f.alloc_vreg(Width::W32, VInit::Const(value));
                    f.push_vreg(operands, v);
                }
                OpCode::LocalGetI32 => {
                    let idx = inline_op.local_index() as usize;
                    let src = f.get_field(locals, idx);
                    f.push_vreg(operands, src);
                }
                OpCode::LocalSetI32 => {
                    let idx = inline_op.local_index() as usize;
                    let val = f.pop(operands, Width::W32);
                    f.set_field(locals, idx, val);
                }
                OpCode::I32Eqz => {
                    let val = f.pop(operands, Width::W32);
                    let zero = f.alloc_vreg(Width::W32, VInit::Const(0));
                    let dst = f.alloc_vreg(Width::W32, VInit::InstDst);
                    f.emit(IrInst::Alu {
                        op: AluOp::Comp(CompOp::Eq),
                        dst,
                        lhs: val,
                        rhs: zero,
                    });
                    f.push_vreg(operands, dst);
                }
                OpCode::I32Add => f.binop(AluOp::Add, operands, Width::W32),
                OpCode::I32Sub => f.binop(AluOp::Sub, operands, Width::W32),
                OpCode::I32LeS => f.binop(AluOp::Comp(CompOp::LeS), operands, Width::W32),
                OpCode::If => {
                    let block_idx = inline_op.immediate_u32();
                    let block = &func.body.blocks[block_idx as usize];
                    let cond = f.pop(operands, Width::W32);
                    let then_block = BlockId::User(pc as u32 + 1);
                    // If there's an else branch, false goes to else_pc+1;
                    // otherwise false skips to end_pc.
                    let false_target = if block.else_pc != 0 {
                        BlockId::User(block.else_pc + 1)
                    } else {
                        BlockId::User(block.end_pc)
                    };
                    f.br_if(cond, then_block, false_target);
                    f.start_block(then_block);
                }
                OpCode::Else => {
                    let block_idx = inline_op.immediate_u32();
                    let end_pc = func.body.blocks[block_idx as usize].end_pc;
                    // End of then-branch — jump over the else body.
                    if !f.is_finalized() {
                        f.br(BlockId::User(end_pc));
                    }
                    f.start_block(BlockId::User(pc as u32 + 1));
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
                        Self::emit_epilogue(
                            &mut f,
                            operands,
                            fibre,
                            lr_preg,
                            fsp_preg,
                            stack_alignment,
                            func,
                        );
                        break;
                    }
                    // Wasm block end — finalize current block if not already done.
                    if !f.is_finalized() {
                        f.br(BlockId::User(pc as u32));
                    }
                    f.start_block(BlockId::User(pc as u32));
                }
                OpCode::Return => Self::emit_epilogue(
                    &mut f,
                    operands,
                    fibre,
                    lr_preg,
                    fsp_preg,
                    stack_alignment,
                    func,
                ),
                OpCode::Call => {
                    let callee_idx = inline_op.immediate_i32();
                    if callee_idx.is_negative() {
                        todo!("call to negative index function");
                    }

                    let func_idx = FunctionIdx::User(callee_idx as u32);
                    let callee = &all_funcs[callee_idx as usize];
                    let callee_sig = func_signature(callee);

                    // Pop args and constrain each to its CC register.
                    for i in (0..callee_sig.params.len()).rev() {
                        let vreg = f.pop(operands, callee_sig.params[i].width());
                        f.set_target(vreg, PReg(i as u8));
                    }

                    f.begin_op("--", "clobber call");

                    // Clobber all live vregs — call will destroy registers.
                    f.clobber_region(locals);
                    f.clobber_region(operands);
                    f.clobber_region(fibre);

                    // Frame advance: the caller's top-of-stack operands
                    // become the callee's params (same stack slots). We
                    // advance g.lb past the caller's frame up to (but not
                    // including) those args, so the callee sees them as
                    // locals[0..N]. See abi.md "Frame advance on calls".
                    //
                    // advance = locals_header_size
                    //         + (operand_depth[pc] - callee_param_slots) * 4
                    let callee_param_slots: u32 = callee.params.iter()
                        .map(|t| slot_size(*t) as u32)
                        .sum();
                    let caller_operand_depth = func.body.operand_depth[pc] as u32;
                    let advance = locals_header_size
                        + (caller_operand_depth - callee_param_slots) * 4;

                    f.begin_op("--", &format!("advance g.lb +{advance}"));

                    // TODO: when callee has more params than CC registers,
                    // overflow params stay on the stack instead of moving
                    // to registers.
                    let lb = f.alloc_vreg(Width::W64, VInit::PReg(lbp_preg));
                    let advance_vreg = f.alloc_vreg(Width::W64, VInit::Const(advance as i64));
                    f.emit(IrInst::Alu {
                        op: AluOp::Add,
                        dst: lb,
                        lhs: lb,
                        rhs: advance_vreg,
                    });

                    f.emit(IrInst::Call { func_idx });

                    f.begin_op("--", &format!("restore g.lb -{advance}"));

                    // Restore g.lb after call returns.
                    let lb = f.alloc_vreg(Width::W64, VInit::PReg(lbp_preg));
                    let advance_vreg = f.alloc_vreg(Width::W64, VInit::Const(advance as i64));
                    f.emit(IrInst::Alu {
                        op: AluOp::Sub,
                        dst: lb,
                        lhs: lb,
                        rhs: advance_vreg,
                    });

                    // Push result vregs — initialized from CC registers.
                    for (i, ty) in callee_sig.results.iter().enumerate() {
                        let v = f.alloc_vreg(ty.width(), VInit::PReg(PReg(i as u8)));
                        f.push_vreg(operands, v);
                    }

                    let fuel = f.alloc_vreg(Width::W64, VInit::PReg(fuel_preg));
                    Self::emit_fuel_check(&mut f, fuel, &mut pending_fuel, pc);
                }
                _ => todo!("unhandled opcode: {:?}", op),
            }

            pc += 1;
        }

        f.build();
        Ok(())
    }

    fn emit_epilogue(
        f: &mut FunctionBuilder,
        operands: VRegionId,
        fibre: VRegionId,
        lr_preg: PReg,
        fsp_preg: PReg,
        stack_alignment: u32,
        func: &FuncMeta,
    ) {
        // Pop results into CC registers.
        for i in (0..func.results.len()).rev() {
            let width = valtype_to_width(&func.results[i]);
            let vreg = f.pop(operands, width);
            f.set_target(vreg, PReg(i as u8));
        }
        Self::emit_native_ret(f, fibre, lr_preg, fsp_preg, stack_alignment);
    }

    /// Restore lr, sp, and emit ret. Shared by normal return and
    /// suspend paths — neither needs to handle wasm-level results.
    fn emit_native_ret(
        f: &mut FunctionBuilder,
        fibre: VRegionId,
        lr_preg: PReg,
        fsp_preg: PReg,
        stack_alignment: u32,
    ) {
        // Restore lr into x30.
        let lr = f.pop(fibre, Width::W64);
        f.set_target(lr, lr_preg);
        f.emit_reg(RegInst::Resolve { vreg: lr });
        // Restore native stack pointer.
        let sp = f.alloc_vreg(Width::W64, VInit::PReg(fsp_preg));
        let frame_size = f.alloc_vreg(Width::W64, VInit::Const(stack_alignment as i64));
        f.emit(IrInst::Alu {
            op: AluOp::Add,
            dst: sp,
            lhs: sp,
            rhs: frame_size,
        });
        f.ret();
    }

    fn emit_fuel_check(f: &mut FunctionBuilder, fuel: VReg, pending_fuel: &mut u32, pc: usize) {
        // Fused subtract-and-compare: subs fuel, fuel, #N
        // LeS makes the backend emit `subs` (flag-setting subtract).
        // Using `fuel` (physical register) as dst writes the result
        // back to fuel while setting flags for the LE condition.

        let op = IrInst::Alu {
            op: AluOp::Comp(CompOp::LeS),
            dst: fuel,
            lhs: fuel,
            rhs: f.alloc_vreg(Width::W32, VInit::Const(*pending_fuel as i64)),
        };
        f.emit(op);
        *pending_fuel = 0;

        let fuel_cond = f.alloc_vreg(Width::W64, VInit::Const(0));
        let suspend_block = f.gen_block();
        let cont_block = BlockId::User(pc as u32);
        f.br_if(fuel_cond, suspend_block, cont_block);

        f.start_block(suspend_block);
        f.ret();

        f.start_block(cont_block);
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
