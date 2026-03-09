use autosynth_codegen::backend::BackendEmitter;
use autosynth_codegen::backend::aarch64::Aarch64Backend;
use autosynth_codegen::{
    AluOp, BlockId, CodeBuilder, CompOp, FunctionBuilder, FunctionIdx, IrInst, IsaReg,
    Operand, Register, VStack, Value, Width,
};
use wust_core::exec::ModuleExecutor;
use wust_core::{
    FRAME_HEADER_SIZE, FuncMeta, OpCode, Outcome, ParsedModule, Task, ValType, slot_size,
};

use crate::CodeBuffer;

/// A JIT-compiled WASM module.
///
/// Owns the parsed module, the autosynth IR compiler state, and an
/// executable code page. For each WASM function, the code page holds
/// an entry trampoline followed by the lowered function body.
///
/// Implements [`ModuleExecutor`] so the runtime can call into JIT code
/// via [`poll`](ModuleExecutor::poll).
pub struct JitModule {
    _module: ParsedModule,
    compiler: CodeBuilder,
    page: CodeBuffer,
    /// Byte offset of each function's entry trampoline within the code page.
    trampoline_offsets: Vec<usize>,
}

impl JitModule {
    /// Compile all functions in the parsed WASM module to native code.
    ///
    /// For each function, builds the autosynth IR, lowers it via the
    /// AArch64 backend, prepends an entry trampoline, and writes
    /// everything into a single executable code page.
    ///
    /// # Errors
    ///
    /// Returns an error if memory mapping or code lowering fails.
    pub fn new(module: ParsedModule) -> Result<Self, anyhow::Error> {
        let mut compiler = CodeBuilder::new();
        let mut page = CodeBuffer::new()?;
        let mut all_code: Vec<u8> = Vec::new();
        let mut trampoline_offsets: Vec<usize> = Vec::new();

        for (func_idx, func) in module.funcs.iter().enumerate() {
            let mut backend = Aarch64Backend::new();
            Self::compile_func(&mut compiler, &mut backend, func_idx as i32, &module.funcs)?;

            let ir_func = &compiler.functions()[compiler.functions().len() - 1];
            let body_bytes = backend.lower(ir_func)?;

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
        })
    }

    /// Access the compiled IR (for debugging/inspection).
    pub fn ir(&self) -> &CodeBuilder {
        &self.compiler
    }

    /// Compile a single WASM function into autosynth IR.
    ///
    /// If a [`Debugger`](autosynth_codegen::Debugger) is attached to `cb`,
    /// source-level annotations are recorded automatically.
    pub fn compile_func(
        cb: &mut CodeBuilder,
        backend: &mut Aarch64Backend,
        func_idx: i32,
        all_funcs: &[FuncMeta],
    ) -> anyhow::Result<()> {
        let func = &all_funcs[func_idx as usize];

        let mut f = FunctionBuilder::new(cb);

        let lbp = backend.use_isa_reg("lbp", IsaReg::FramePointer);
        let lr = backend.use_isa_reg("lr", IsaReg::ReturnAddress);
        let fuel = backend.use_isa_reg("fuel", IsaReg::Define64(0));
        let _ctx = backend.use_isa_reg("ctx", IsaReg::Define64(1));
        let fsp = backend.use_isa_reg("fsp", IsaReg::StackPointer);

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

        // Declare parameters
        f.begin_op("--", "params_start");
        for (i, param) in func.params.iter().enumerate() {
            f.define_slot(locals, i, valtype_to_width(param), Value::Param(i));
        }

        f.begin_op("--", "locals_start");
        // Declare zero-initialized locals
        for (i, local) in func.locals.iter().enumerate() {
            f.define_slot(
                locals,
                i + func.params.len(),
                valtype_to_width(&local),
                Value::ConstI64(0),
            );
        }

        f.begin_op("--", "prologue");
        f.push(fibre, Width::W64, Value::Reg(lr));

        // Finalize entry block, branch to first user block.
        f.br(BlockId::User(0));
        f.start_block(BlockId::User(0));

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

            f.begin_op(&pc.to_string(), &format!("{op}"));

            // Accrue fuel cost for this opcode.
            pending_fuel += op.fuel_cost();

            match op {
                OpCode::I32Const => {
                    f.push(
                        operands,
                        Width::W32,
                        Value::ConstI32(inline_op.immediate_i32()),
                    );
                }

                OpCode::LocalGetI32 => {
                    let idx = inline_op.local_index();
                    let src = f.get_slot(locals, idx as usize);
                    f.push(operands, Width::W32, Value::VReg(src));
                }
                OpCode::LocalSetI32 => {
                    let idx = inline_op.local_index();
                    let val = f.pop(operands, Width::W32);
                    f.define_slot(locals, idx as usize, Width::W32, Value::VReg(val));
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
                        // Function end — pop return value and fibre LR, then return.
                        let values = if f.stack_depth(operands) > 0 {
                            vec![f.pop(operands, Width::W32)]
                        } else {
                            vec![]
                        };
                        f.pop(fibre, Width::W64);
                        f.ret(values, false);
                        break;
                    }
                    // Wasm block end — finalize current block if not already done.
                    if !f.is_finalized() {
                        f.br(BlockId::User(pc as u32));
                    }
                    f.start_block(BlockId::User(pc as u32));
                }

                OpCode::Return => {
                    let val = f.pop(operands, Width::W32);
                    f.pop(fibre, Width::W64);
                    f.ret(vec![val], false);
                }

                OpCode::Call => {
                    let callee_idx = inline_op.immediate_i32();
                    if callee_idx.is_negative() {
                        todo!("call to negative index function");
                    }
                    let callee = &all_funcs[callee_idx as usize];
                    let frame_advance = func.locals_size as u32 + FRAME_HEADER_SIZE as u32;

                    let mut args: Vec<_> = (0..callee.param_count())
                        .map(|_| f.pop(operands, Width::W32))
                        .collect();
                    args.reverse();

                    let result_vregs: Vec<_> = (0..callee.result_count())
                        .map(|_| f.push_dst(operands, Width::W32))
                        .collect();

                    f.emit(IrInst::Call {
                        func_idx: FunctionIdx::User(callee_idx as u32),
                        args,
                        results: result_vregs,
                        frame_advance,
                    });

                    // Fused subtract-and-compare: subs fuel, fuel, #N
                    // LeS makes the backend emit `subs` (flag-setting subtract).
                    // Using `fuel` (physical register) as dst writes the result
                    // back to fuel while setting flags for the LE condition.
                    let fuel_cond = f.alloc_temp(Width::W32, Value::ConstI64(0));
                    f.emit(IrInst::Alu {
                        op: AluOp::Comp(CompOp::LeS),
                        dst: fuel,
                        lhs: Operand::from(fuel),
                        rhs: Operand::Imm32(pending_fuel as i32),
                    });
                    pending_fuel = 0;

                    let suspend_block = f.gen_block();
                    let cont_block = BlockId::User(pc as u32);

                    f.br_if(fuel_cond, suspend_block, cont_block);

                    f.start_block(suspend_block);
                    f.ret(Vec::new(), false);

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

fn valtype_to_width(ty: &ValType) -> Width {
    match ty {
        ValType::I32 => Width::W32,
        ValType::I64 => Width::W64,
        ValType::F32 => todo!("F32: needs float register class"),
        ValType::F64 => todo!("F64: needs float register class"),
        ValType::V128 => todo!("V128: needs vector register class"),
        ValType::Ref(_) => todo!("Ref types not yet supported"),
    }
}

/// Generate the entry trampoline as raw machine code bytes.
///
/// The trampoline bridges the inline-asm calling convention to the
/// JIT function body:
///
/// 1. Save lr on fibre stack (x28)
/// 2. Convert x29 from wasm_fp.ptr to locals base (g.lb)
/// 3. Load parameters from local slots into x9+
/// 4. bl to function body
/// 5. Restore x29 to wasm_fp.ptr
/// 6. Store results from x9+ to operand base
/// 7. Restore lr from fibre stack
/// 8. ret
fn emit_entry_trampoline(func: &FuncMeta) -> Vec<u8> {
    let locals_header_size = func.locals_size as u32 + FRAME_HEADER_SIZE as u32;
    let mut words: Vec<u32> = Vec::with_capacity(16);

    // str x30, [x28, #-16]!   — save lr on fibre stack (16-byte aligned)
    words.push(encode_str_pre(30, 28, -16));

    // sub x29, x29, #locals_header_size  — convert to locals base
    words.push(encode_sub_imm_x(29, 29, locals_header_size));

    // Load parameters from local slots into calling convention regs (x9, x10, ...)
    for (i, &off) in func.local_byte_offsets[..func.param_count()]
        .iter()
        .enumerate()
        .take(7)
    {
        // ldr w(9+i), [x29, #off]  — 32-bit unsigned offset load
        words.push(encode_ldr_w_uoff(9 + i as u32, 29, off as u32));
    }

    // bl to function body — offset in words from this instruction
    // Body starts right after the trampoline.
    let bl_word_idx = words.len();
    // Total trampoline size = bl_word_idx + 1 (bl) + 1 (add) + results (str) + 1 (ldr_post) + 1 (ret)
    let total_trampoline = bl_word_idx + 1 + 1 + func.result_count().min(7) + 1 + 1;
    let bl_offset = total_trampoline as i32 - bl_word_idx as i32;
    words.push(encode_bl(bl_offset));

    // add x29, x29, #locals_header_size  — restore to wasm_fp.ptr
    words.push(encode_add_imm_x(29, 29, locals_header_size));

    // Store results from calling convention regs to operand base (wasm_fp.ptr = x29)
    let mut result_offset = 0u32;
    for (i, ty) in func.results.iter().enumerate().take(7) {
        // str w(9+i), [x29, #result_offset]
        words.push(encode_str_w_uoff(9 + i as u32, 29, result_offset));
        result_offset += slot_size(*ty) as u32 * 4;
    }

    // ldr x30, [x28], #16  — restore lr from fibre stack
    words.push(encode_ldr_post(30, 28, 16));

    // ret x30
    words.push(encode_ret(30));

    debug_assert_eq!(
        words.len(),
        total_trampoline,
        "trampoline size mismatch: predicted {total_trampoline}, got {}",
        words.len()
    );

    let mut bytes = Vec::with_capacity(words.len() * 4);
    for word in words {
        bytes.extend_from_slice(&word.to_le_bytes());
    }
    bytes
}

// --- Raw aarch64 instruction encoders for the trampoline ---

/// `str Xt, [Xn, #simm9]!` (pre-index, 64-bit)
fn encode_str_pre(rt: u32, rn: u32, imm9: i32) -> u32 {
    let imm9_bits = ((imm9 as u32) & 0x1FF) << 12;
    0xF8000C00 | imm9_bits | (rn << 5) | rt
}

/// `ldr Xt, [Xn], #simm9` (post-index, 64-bit)
fn encode_ldr_post(rt: u32, rn: u32, imm9: i32) -> u32 {
    let imm9_bits = ((imm9 as u32) & 0x1FF) << 12;
    0xF8400400 | imm9_bits | (rn << 5) | rt
}

/// `sub Xd, Xn, #imm12` (64-bit)
fn encode_sub_imm_x(rd: u32, rn: u32, imm12: u32) -> u32 {
    debug_assert!(imm12 < 4096, "imm12 out of range: {imm12}");
    0xD1000000 | (imm12 << 10) | (rn << 5) | rd
}

/// `add Xd, Xn, #imm12` (64-bit)
fn encode_add_imm_x(rd: u32, rn: u32, imm12: u32) -> u32 {
    debug_assert!(imm12 < 4096, "imm12 out of range: {imm12}");
    0x91000000 | (imm12 << 10) | (rn << 5) | rd
}

/// `ldr Wt, [Xn, #uimm12*4]` (32-bit unsigned offset)
fn encode_ldr_w_uoff(rt: u32, rn: u32, byte_offset: u32) -> u32 {
    debug_assert!(
        byte_offset % 4 == 0,
        "offset must be 4-byte aligned: {byte_offset}"
    );
    let scaled = byte_offset / 4;
    debug_assert!(scaled < 4096, "scaled offset out of range: {scaled}");
    0xB9400000 | (scaled << 10) | (rn << 5) | rt
}

/// `str Wt, [Xn, #uimm12*4]` (32-bit unsigned offset)
fn encode_str_w_uoff(rt: u32, rn: u32, byte_offset: u32) -> u32 {
    debug_assert!(
        byte_offset % 4 == 0,
        "offset must be 4-byte aligned: {byte_offset}"
    );
    let scaled = byte_offset / 4;
    debug_assert!(scaled < 4096, "scaled offset out of range: {scaled}");
    0xB9000000 | (scaled << 10) | (rn << 5) | rt
}

/// `bl #offset` (offset in words, signed 26-bit)
fn encode_bl(word_offset: i32) -> u32 {
    let imm26 = (word_offset as u32) & 0x03FFFFFF;
    0x94000000 | imm26
}

/// `ret Xn`
fn encode_ret(rn: u32) -> u32 {
    0xD65F0000 | (rn << 5)
}

impl ModuleExecutor for JitModule {
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

/// Call the JIT entry trampoline with the appropriate register setup.
///
/// Register convention on entry to trampoline:
/// - x0  = fuel counter (g.fuel)
/// - x29 = wasm_fp.ptr (operand base, past header)
/// - x28 = fibre stack pointer
///
/// The trampoline converts x29 to locals base, loads params,
/// calls the function body, stores results, and returns.
fn call_trampoline(trampoline_ptr: *const u8, ctx: &mut wust_core::Context) -> Outcome {
    const FUEL: usize = std::mem::offset_of!(wust_core::Context, fuel);
    const WASM_FP: usize = std::mem::offset_of!(wust_core::Context, wasm_fp);
    const FIBRE_SP: usize = std::mem::offset_of!(wust_core::Context, fibre_sp);

    let ctx_ptr = ctx as *mut wust_core::Context as u64;

    unsafe {
        std::arch::asm!(
            // Save host callee-saved registers.
            "stp x29, x30, [sp, #-16]!",
            "stp x28, x27, [sp, #-16]!",
            "stp x26, x25, [sp, #-16]!",
            "stp x24, x23, [sp, #-16]!",
            "stp x22, x21, [sp, #-16]!",
            "stp x20, x19, [sp, #-16]!",

            // Save ctx pointer on native stack so it survives across the JIT
            // call (any register may be clobbered by the JIT).
            "str {ctx}, [sp, #-16]!",

            // Load JIT state from context.
            "ldr x0, [{ctx}, #{fuel}]",
            "ldr x29, [{ctx}, #{fp}]",
            "ldr x28, [{ctx}, #{fibre_sp}]",

            // Call the entry trampoline.
            "blr {code}",

            // After JIT returns, x0 = fuel, x29 = wasm_fp, x28 = fibre_sp.
            // Reload ctx pointer from stack, then store JIT state back.
            "ldr x1, [sp], #16",
            "str x0, [x1, #{fuel}]",
            "str x29, [x1, #{fp}]",
            "str x28, [x1, #{fibre_sp}]",

            // Restore host callee-saved registers.
            "ldp x20, x19, [sp], #16",
            "ldp x22, x21, [sp], #16",
            "ldp x24, x23, [sp], #16",
            "ldp x26, x25, [sp], #16",
            "ldp x28, x27, [sp], #16",
            "ldp x29, x30, [sp], #16",

            ctx = in(reg) ctx_ptr,
            code = in(reg) trampoline_ptr,
            fuel = const FUEL,
            fp = const WASM_FP,
            fibre_sp = const FIBRE_SP,
            // Clobbers: all caller-saved registers the JIT might use.
            out("x0") _, out("x1") _, out("x2") _,
            out("x3") _, out("x4") _, out("x5") _,
            out("x6") _, out("x7") _, out("x8") _,
            out("x9") _, out("x10") _, out("x11") _,
            out("x12") _, out("x13") _, out("x14") _,
            out("x15") _, out("x16") _, out("x17") _,
        );
    }

    Outcome::Return
}
