pub use autosynth_test_utils::assert_stream_eq;

use autosynth_codegen::ir::IrFunction;
use autosynth_codegen::pipeline::compile;
use autosynth_emit_aarch64::Aarch64Emitter;
use autosynth_emitter::{CodeContext, Emitter};
use autosynth_ir::{AluOp, BlockId, FunctionIdx, Label};
use autosynth_isa::Width;
use autosynth_select_aarch64::Aarch64Selector;
use wust_codegen::CodeBuffer;
use wust_codegen::wasm_builder::WasmFunctionBuilder;
use wust_core::{FRAME_HEADER_SIZE, FuncMeta, OpCode, ParsedModule, slot_size};

pub fn parse_wat(wat: &str) -> ParsedModule {
    let bytes = wat::parse_str(wat).expect("parse WAT");
    ParsedModule::new(&bytes).expect("parse module")
}

pub fn compile_func(module: &ParsedModule, func_idx: usize) -> IrFunction {
    let func = &module.funcs[func_idx];
    let mut f = WasmFunctionBuilder::new(func);

    let mut pc = 0;
    loop {
        let inline_op = &func.body.ops[pc];
        let op = inline_op.opcode();

        match op {
            OpCode::I32Const => f.push_const(inline_op.immediate_i32() as i64, Width::W32),
            OpCode::LocalGetI32 => f.push_local(inline_op.local_index() as usize),
            OpCode::LocalSetI32 => {
                let val = f.pop();
                f.local_set(inline_op.local_index() as usize, val);
            }
            OpCode::I32Eqz => f.eqz(),
            OpCode::I32Add => f.binop(AluOp::Add, Width::W32),
            OpCode::I32Sub => f.binop(AluOp::Sub, Width::W32),
            OpCode::If => {
                let block_idx = inline_op.immediate_u32();
                let block = &func.body.blocks[block_idx as usize];
                let cond = f.pop();
                let then_block = BlockId::User(pc as u32 + 1);
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
                f.br(BlockId::User(end_pc));
                f.start_block(BlockId::User(pc as u32 + 1));
            }
            OpCode::End => {
                let block_idx = inline_op.immediate_u32();
                if block_idx == 0 {
                    f.emit_return(func);
                    break;
                }
                f.br(BlockId::User(pc as u32));
                f.start_block(BlockId::User(pc as u32));
            }
            _ => todo!("unhandled opcode: {:?}", op),
        }

        pc += 1;
    }

    f.build()
}

/// Full pipeline: IR → select → emit → executable.
pub fn jit_compile(module: &ParsedModule, func_idx: usize) -> JitFunction {
    let func_meta = &module.funcs[func_idx];
    let mut ir_func = compile_func(module, func_idx);

    let mut selector = Aarch64Selector::new(ir_func.alloc.clone());
    let vcode = compile(&ir_func, &mut selector).unwrap();

    let func_idx = FunctionIdx::User(func_idx as u32);
    let mut page = CodeBuffer::new().unwrap();
    let mut emitter = Aarch64Emitter::new(func_idx);
    for &block_id in &vcode.block_order {
        page.mark_label(Label::Block(func_idx, block_id));
        let mut block_stream = vcode.blocks[&block_id].clone();
        emitter.emit(&mut block_stream, &mut page).unwrap();
    }
    emitter.finalize(&mut page).unwrap();
    page.flash().unwrap();

    // Compute frame layout for the trampoline.
    let locals_size: u32 = func_meta
        .params
        .iter()
        .chain(func_meta.locals.iter())
        .map(|t| slot_size(*t) as u32)
        .sum();
    let locals_header_size = locals_size + FRAME_HEADER_SIZE as u32;

    JitFunction {
        page,
        locals_size,
        locals_header_size,
        num_params: func_meta.params.len(),
        num_results: func_meta.results.len(),
    }
}

/// A JIT-compiled function backed by executable memory.
///
/// Includes frame layout metadata for the trampoline to set up
/// the managed stack correctly.
pub struct JitFunction {
    page: CodeBuffer,
    locals_size: u32,
    locals_header_size: u32,
    num_params: usize,
    num_results: usize,
}

impl JitFunction {
    /// Call with one i32 argument, return i32 result.
    ///
    /// Sets up a managed stack frame per the wust ABI:
    /// - x29 (g.lb) points to the frame base
    /// - Param written to [x29 + 0]
    /// - Param also in x0 (CC register)
    /// - After return, result read from x0
    pub fn call_i32(&self, arg: i32) -> i32 {
        // Allocate managed stack space.
        let mut managed_stack = [0u8; 4096];
        let frame_base = managed_stack.as_mut_ptr();

        // Write param to the managed stack (canonical ABI).
        unsafe {
            *(frame_base as *mut i32) = arg;
        }

        let func_ptr = self.page.entry();
        let result: i64;
        unsafe {
            std::arch::asm!(
                "blr {trampoline}",
                trampoline = in(reg) trampoline_call_i32 as *const (),
                in("x0") func_ptr as u64,
                in("x1") frame_base as u64,
                in("x2") arg as i64,
                lateout("x0") result,
                clobber_abi("C"),
            );
        }
        result as i32
    }
}

/// Naked trampoline — sets up x29 (g.lb) and calls the JIT function.
///
/// `extern "custom"` — no params, no return type. Everything through
/// registers. The caller sets up:
///   x0 = JIT function pointer
///   x1 = managed stack frame base (becomes x29)
///   x2 = i32 param (placed in x0 for CC)
///
/// Returns result in x0.
#[unsafe(naked)]
unsafe extern "custom" fn trampoline_call_i32() {
    std::arch::naked_asm!(
        // Save caller's frame pointer and link register.
        "stp x29, x30, [sp, #-16]!",
        // Save func pointer to a temp register before we clobber x0.
        "mov x3, x0",
        // Set up g.lb (x29) = managed stack frame base.
        "mov x29, x1",
        // Move param to x0 (CC register for the JIT function).
        "mov x0, x2",
        // Call JIT function.
        "blr x3",
        // Result is in x0 — return it.
        // Restore caller's frame pointer and link register.
        "ldp x29, x30, [sp], #16",
        "ret",
    );
}
