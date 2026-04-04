//! Wasm bytecode → builder graph compilation.

use wust_core::{FuncIdx, FuncMeta, OpCode};

use super::Width;
use super::function::WasmFunctionBuilder;
use crate::{
    VCode, VInit,
    builder::{BlockId, graph::WasmGraph},
    op::{AluOp, CmpOp},
    types::Abi,
};

/// Compile a wasm function to graph IR.
pub fn compile(func_idx: FuncIdx, funcs: &[FuncMeta]) -> WasmGraph {
    let meta = &funcs[*func_idx as usize];
    let mut func = WasmFunctionBuilder::new(meta);

    let mut pc = 0;
    loop {
        let inline_op = &meta.body.ops[pc];
        let op = inline_op.opcode();

        let block = func.block();

        match op {
            OpCode::I32Const => block.define_and_push(
                "operands",
                VInit {
                    width: Width::W32,
                    constant: Some(inline_op.immediate_i32() as i64),
                    preg: None,
                    mem: None,
                },
            ),
            OpCode::LocalGetI32 => {
                block.push_local_get(inline_op.local_index() as usize, Width::W32)
            }
            OpCode::LocalSetI32 => {
                block.pop_local_set(inline_op.local_index() as usize, Width::W32)
            }
            OpCode::I32Add => block.binop(AluOp::Add, Width::W32),
            OpCode::I32Sub => block.binop(AluOp::Sub, Width::W32),
            OpCode::I32Mul => block.binop(AluOp::Mul, Width::W32),
            OpCode::I32LeS => block.binop(AluOp::Cmp(CmpOp::LeS), Width::W32),
            OpCode::I32Eqz => {
                block.define_and_push(
                    "operands",
                    VInit {
                        width: Width::W32,
                        constant: Some(0),
                        preg: None,
                        mem: None,
                    },
                );

                block.binop(AluOp::Cmp(CmpOp::Eq), Width::W32);
            }

            OpCode::If => {
                let block_idx = inline_op.immediate_u32();
                let target_block = &meta.body.blocks[block_idx as usize];
                let if_false = BlockId::User(target_block.end_pc);
                let if_true = BlockId::User(pc as u32 + 1);
                let (input, _) = block.pop("operands");
                func.brif(input, if_true, if_false);
                func.switch_to(if_true);
            }
            OpCode::Else => {
                todo!();
            }
            OpCode::End => {
                let block_idx = inline_op.immediate_u32();

                // Implicit return at end of function body
                // If the last operation emitted wasn't a return,
                // then we must emit one
                if block_idx == 0 {
                    let block = func.block();
                    match block
                        .operations
                        .last()
                        .map(|&key| block.state.borrow().operations.get(key).unwrap().opcode)
                    {
                        Some(VCode::Return { .. }) => break,
                        _ => {
                            func.emit_return(Abi::WasmJit);
                            break;
                        }
                    }
                }

                let target_block = &meta.body.blocks[block_idx as usize];
                let end_id = BlockId::User(target_block.end_pc);

                func.switch_to(end_id);
            }
            OpCode::Call => {
                let callee_idx = FuncIdx::new(inline_op.immediate_u32());
                block.emit_call(callee_idx, funcs, BlockId::Entry(0), Abi::WasmJit);
            }
            OpCode::Return => {
                func.emit_return(Abi::WasmJit);
            }
            _ => todo!("unhandled opcode: {:?}", op),
        }

        pc += 1;
    }

    WasmGraph::from(func)
}
