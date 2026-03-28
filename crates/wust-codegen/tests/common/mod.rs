use autosynth_codegen::builder::IrFunction;
use autosynth_codegen::pipeline::{compile, trivial_regalloc, VCodeFunction};
use autosynth_emit_aarch64::Aarch64Emitter;
use autosynth_emitter::Emitter;
use autosynth_ir::{AluOp, BlockId, VCode};
use autosynth_isa::Width;
use autosynth_select_aarch64::Aarch64Selector;
use wust_codegen::wasm_builder::WasmFunctionBuilder;
use wust_codegen::CodeBuffer;
use wust_core::{OpCode, ParsedModule};

pub fn parse_wat(wat: &str) -> ParsedModule {
    let bytes = wat::parse_str(wat).expect("parse WAT");
    ParsedModule::new(&bytes).expect("parse module")
}

/// Compile a single wasm function to IR using the new VCode pipeline.
pub fn compile_func(module: &ParsedModule, func_idx: usize) -> IrFunction {
    let func = &module.funcs[func_idx];

    let mut f = WasmFunctionBuilder::new();
    f.start_block(BlockId::Entry);

    for (i, param) in func.params.iter().enumerate() {
        f.declare_param(i, valtype_to_width(param));
    }

    for local in func.locals.iter() {
        f.declare_local(valtype_to_width(local));
    }

    let mut pc = 0;
    loop {
        let inline_op = &func.body.ops[pc];
        let op = inline_op.opcode();

        match op {
            OpCode::I32Const => {
                let value = inline_op.immediate_i32();
                f.push_const(value as i64, Width::W32);
            }
            OpCode::LocalGetI32 => {
                let idx = inline_op.local_index() as usize;
                f.push_local(idx);
            }
            OpCode::I32Add => f.binop(AluOp::Add, Width::W32),
            OpCode::I32Sub => f.binop(AluOp::Sub, Width::W32),
            OpCode::End => {
                let block_idx = inline_op.immediate_u32();
                if block_idx == 0 {
                    f.emit_return();
                    break;
                }
            }
            _ => todo!("unhandled opcode: {:?}", op),
        }

        pc += 1;
    }

    f.build()
}

/// Full pipeline: IR → select → regalloc → emit → executable.
pub fn jit_compile(module: &ParsedModule, func_idx: usize) -> JitFunction {
    let func = compile_func(module, func_idx);

    // Pass 1: instruction selection
    let mut selector = Aarch64Selector::new();
    let mut vcode = compile(func, &mut selector).unwrap();

    // Pass 2: trivial register allocation
    trivial_regalloc(&mut vcode);

    // Emit into CodeBuffer
    let mut page = CodeBuffer::new().unwrap();
    let mut emitter = Aarch64Emitter::new();
    for &block_id in &vcode.block_order {
        let block = &vcode.blocks[&block_id];
        let mut ops = block.operands.iter().copied();
        for inst in &block.instructions {
            emitter.emit(inst, &mut ops, &mut page).unwrap();
        }
    }
    page.finish().unwrap();

    JitFunction { _page: page }
}

/// A JIT-compiled function backed by executable memory.
pub struct JitFunction {
    _page: CodeBuffer,
}

impl JitFunction {
    pub fn call_i32(&self, arg: i32) -> i32 {
        let result: i64;
        unsafe {
            std::arch::asm!(
                "blr {func}",
                func = in(reg) self._page.entry(),
                in("x0") arg as i64,
                lateout("x0") result,
                clobber_abi("C"),
            );
        }
        result as i32
    }
}

fn valtype_to_width(vt: &wust_core::ValType) -> Width {
    match vt {
        wust_core::ValType::I32 => Width::W32,
        wust_core::ValType::I64 => Width::W64,
        _ => todo!(),
    }
}
