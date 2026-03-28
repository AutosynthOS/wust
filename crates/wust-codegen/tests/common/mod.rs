use autosynth_codegen::builder::IrFunction;
use autosynth_ir::{AluOp, BlockId, VCode};
use autosynth_isa::Width;
use wust_codegen::wasm_builder::WasmFunctionBuilder;
use wust_core::{FuncMeta, OpCode, ParsedModule};

pub fn parse_wat(wat: &str) -> ParsedModule {
    let bytes = wat::parse_str(wat).expect("parse WAT");
    ParsedModule::new(&bytes).expect("parse module")
}

/// Compile a single wasm function to IR using the new VCode pipeline.
pub fn compile_func(module: &ParsedModule, func_idx: usize) -> IrFunction {
    let func = &module.funcs[func_idx];

    let mut f = WasmFunctionBuilder::new();
    f.start_block(BlockId::Entry);

    // Declare params.
    for (i, param) in func.params.iter().enumerate() {
        f.declare_param(i, valtype_to_width(param));
    }

    // Declare locals.
    for local in func.locals.iter() {
        f.declare_local(valtype_to_width(local));
    }

    // Walk wasm opcodes.
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

fn valtype_to_width(vt: &wust_core::ValType) -> Width {
    match vt {
        wust_core::ValType::I32 => Width::W32,
        wust_core::ValType::I64 => Width::W64,
        _ => todo!(),
    }
}
