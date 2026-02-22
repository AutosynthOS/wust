use crate::Module;
use crate::parse::body::{BlockKind, OpCode};
use crate::parse::func::ParsedFunction;
use crate::stack::Stack;

/// Trap reasons that can occur during execution.
/// Stack-allocated, no heap — keeps the hot loop cheap.
#[derive(Debug)]
pub(crate) enum Trap {
    Unreachable,
    FuncNotFound(u32),
}

impl std::fmt::Display for Trap {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Trap::Unreachable => write!(f, "unreachable executed"),
            Trap::FuncNotFound(idx) => write!(f, "function {idx} not found"),
        }
    }
}

impl std::error::Error for Trap {}

/// Saved caller state, pushed onto the call stack on `call`,
/// popped on function `end`/`return`.
struct SavedFrame {
    pc: usize,
    func_idx: usize,
    return_sp: usize,
    locals_sp: usize,
    result_count: u32,
}

/// Entry point: set up the first frame and run the interpreter loop.
pub(crate) fn call_function(
    module: &Module,
    stack: &mut Stack,
    func: &ParsedFunction,
    func_idx: usize,
    arg_count: usize,
) -> Result<(), Trap> {
    let return_sp = stack.sp() - arg_count * 8;
    let locals_sp = return_sp;
    let local_count = func.locals.len();

    for _ in arg_count..local_count {
        stack.push_u64(0);
    }

    execute(module, stack, func, func_idx, return_sp, locals_sp)
}

fn execute(
    module: &Module,
    stack: &mut Stack,
    initial_func: &ParsedFunction,
    initial_func_idx: usize,
    initial_return_sp: usize,
    initial_locals_sp: usize,
) -> Result<(), Trap> {
    let mut call_stack: Vec<SavedFrame> = Vec::new();

    // Current frame state — kept as locals, not on the heap.
    let mut pc: usize = 0;
    let mut func = initial_func;
    let mut func_idx = initial_func_idx;
    let mut return_sp = initial_return_sp;
    let mut locals_sp = initial_locals_sp;
    let mut result_count = func.results.len() as u32;

    loop {
        if pc >= func.body.ops.len() {
            break;
        }

        let entry = func.body.ops[pc];
        pc += 1;

        let opcode = entry.opcode();
        let imm = entry.immediate_u32();

        match opcode {
            OpCode::Nop => {}

            OpCode::Unreachable => return Err(Trap::Unreachable),

            OpCode::Return => {
                copy_results(stack, return_sp, result_count);
                match call_stack.pop() {
                    Some(saved) => {
                        func = &module.funcs[saved.func_idx];
                        pc = saved.pc;
                        return_sp = saved.return_sp;
                        locals_sp = saved.locals_sp;
                        result_count = saved.result_count;
                    }
                    None => break,
                }
            }

            // --- Block control flow ---

            OpCode::Block | OpCode::Loop => {}

            OpCode::If => {
                let condition = stack.pop_i32();
                if condition == 0 {
                    let block = &func.body.blocks[imm as usize];
                    if block.else_pc != 0 {
                        pc = block.else_pc as usize + 1;
                    } else {
                        pc = block.end_pc as usize + 1;
                    }
                }
            }

            OpCode::Else => {
                let block = &func.body.blocks[imm as usize];
                pc = block.end_pc as usize + 1;
            }

            OpCode::End => {
                let block = &func.body.blocks[imm as usize];
                if block.kind == BlockKind::Function {
                    copy_results(stack, return_sp, result_count);
                    match call_stack.pop() {
                        Some(saved) => {
                            func = &module.funcs[saved.func_idx];
                            pc = saved.pc;
                            return_sp = saved.return_sp;
                            locals_sp = saved.locals_sp;
                            result_count = saved.result_count;
                        }
                        None => break,
                    }
                }
            }

            // --- Call ---

            OpCode::Call => {
                let callee_idx = imm as usize;
                let callee = module
                    .funcs
                    .get(callee_idx)
                    .ok_or(Trap::FuncNotFound(imm))?;

                call_stack.push(SavedFrame {
                    pc,
                    func_idx,
                    return_sp,
                    locals_sp,
                    result_count,
                });

                let arg_count = callee.param_count();
                let new_return_sp = stack.sp() - arg_count * 8;
                let new_locals_sp = new_return_sp;

                for _ in arg_count..callee.locals.len() {
                    stack.push_u64(0);
                }

                func = callee;
                func_idx = callee_idx;
                pc = 0;
                return_sp = new_return_sp;
                locals_sp = new_locals_sp;
                result_count = callee.results.len() as u32;
            }

            // --- Stack operations ---

            OpCode::I32Const => {
                let val = (imm as i32) << 8 >> 8;
                stack.push_i32(val);
            }

            OpCode::I32Add => {
                let b = stack.pop_i32();
                let a = stack.pop_i32();
                stack.push_i32(a.wrapping_add(b));
            }

            OpCode::I32Sub => {
                let b = stack.pop_i32();
                let a = stack.pop_i32();
                stack.push_i32(a.wrapping_sub(b));
            }

            OpCode::I32LeS => {
                let b = stack.pop_i32();
                let a = stack.pop_i32();
                stack.push_i32((a <= b) as i32);
            }

            OpCode::RefNull => {
                stack.push_u64(0);
            }

            OpCode::LocalGet => {
                let offset = locals_sp + (imm as usize) * 8;
                let val = stack.read_u64_at(offset);
                stack.push_u64(val);
            }

            OpCode::LocalSet => {
                let val = stack.pop_u64();
                let offset = locals_sp + (imm as usize) * 8;
                stack.write_u64_at(offset, val);
            }

            OpCode::LocalTee => {
                let val = stack.read_u64_at(stack.sp() - 8);
                let offset = locals_sp + (imm as usize) * 8;
                stack.write_u64_at(offset, val);
            }

            // TODO: globals storage not implemented yet.
            OpCode::GlobalGet => {
                stack.push_u64(0);
            }
            OpCode::GlobalSet => {
                stack.pop_u64();
            }

            _ => {}
        }
    }

    Ok(())
}

/// Copy the top `result_count` values to `return_sp`, then reset SP.
#[inline(always)]
fn copy_results(stack: &mut Stack, return_sp: usize, result_count: u32) {
    let count = result_count as usize;
    let src = stack.sp() - count * 8;

    for i in 0..count {
        let val = stack.read_u64_at(src + i * 8);
        stack.write_u64_at(return_sp + i * 8, val);
    }

    stack.set_sp(return_sp + count * 8);
}
