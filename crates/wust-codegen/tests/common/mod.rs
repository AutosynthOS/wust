use autosynth_codegen::ir::IrFunction;
use autosynth_codegen::pipeline::compile;
use autosynth_emit_aarch64::Aarch64Emitter;
use autosynth_emitter::Emitter;
use autosynth_ir::{AluOp, BlockId};
use autosynth_isa::Width;
use autosynth_select_aarch64::Aarch64Selector;
use wust_codegen::wasm_builder::WasmFunctionBuilder;
use wust_codegen::CodeBuffer;
use wust_core::{OpCode, ParsedModule};

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
            OpCode::I32Add => f.binop(AluOp::Add, Width::W32),
            OpCode::I32Sub => f.binop(AluOp::Sub, Width::W32),
            OpCode::End => {
                if inline_op.immediate_u32() == 0 {
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

pub fn jit_compile(module: &ParsedModule, func_idx: usize) -> JitFunction {
    let func = compile_func(module, func_idx);

    let mut selector = Aarch64Selector::new();
    let vcode = compile(func, &mut selector).unwrap();

    let mut page = CodeBuffer::new().unwrap();
    let mut emitter = Aarch64Emitter::new();
    for &block_id in &vcode.block_order {
        let block = &vcode.blocks[&block_id];
        let mut ops = block.operands.iter().copied();
        for inst in &block.instructions {
            emitter.emit(inst, &mut ops, &mut page).unwrap();
        }
    }
    page.flash().unwrap();

    JitFunction { _page: page }
}

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
