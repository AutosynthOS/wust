//! Recursive interpreter for WASM bytecode.
//!
//! Control flow is expressed through Rust recursion — each block/loop/if
//! becomes a recursive call to `interpret_block`. No explicit control stack.

use super::helpers::{
    check_indirect_type, coerce_bits_to_global, execute_memory_init, execute_table_copy,
    execute_table_init, resolve_table_element,
};
use super::stack::Stack;
use crate::runtime::error::ExecError;
use crate::runtime::module::{Func, Module};
use crate::runtime::opcode::*;
use crate::runtime::store::{EXTERN_FUNC_BASE, Store};
use crate::runtime::value::{Value, wasm_max, wasm_min, wasm_nearest};

// ---------------------------------------------------------------------------
// Pop helpers — all values stored as u64 (8-byte slots).
// ---------------------------------------------------------------------------

#[inline(always)]
fn pop_i32(stack: &mut Stack) -> i32 {
    stack.pop_u64() as u32 as i32
}

#[inline(always)]
fn pop_i64(stack: &mut Stack) -> i64 {
    stack.pop_u64() as i64
}

#[inline(always)]
fn pop_f32(stack: &mut Stack) -> f32 {
    f32::from_bits(stack.pop_u64() as u32)
}

#[inline(always)]
fn pop_f64(stack: &mut Stack) -> f64 {
    f64::from_bits(stack.pop_u64())
}

#[inline(always)]
fn pop_raw(stack: &mut Stack) -> u64 {
    stack.pop_u64()
}

/// Pop params from the stack, call a host function, push results.
fn call_host(
    stack: &mut Stack,
    host_fn: &dyn Fn(&[Value], &mut [u8]) -> Result<Vec<Value>, String>,
    param_types: &[wasmparser::ValType],
    memory: &mut [u8],
) -> Result<(), ExecError> {
    let count = param_types.len();
    let base = stack.sp() - count as u32 * 8;
    let args: Vec<Value> = param_types
        .iter()
        .enumerate()
        .map(|(i, &ty)| Value::from_bits(stack.read_u64(base + i as u32 * 8), ty))
        .collect();
    stack.set_sp(base);
    let results = host_fn(&args, memory).map_err(|e| ExecError::Trap(format!("trap: {e}")))?;
    for r in results {
        stack.push_u64(r.to_bits());
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Control flow result — replaces the explicit control stack.
// ---------------------------------------------------------------------------

/// Result of interpreting a block of instructions.
///
/// Rust's call stack is the control stack. `br` returns `Branch(depth)`
/// which unwinds through recursive calls until the target block handles it.
enum Flow {
    /// Block completed normally (fell through to end).
    Normal,
    /// Branch with remaining depth. depth=0 means "targeting this block."
    Branch(u32),
    /// Function return — unwinds all blocks in the current function.
    Return,
}

// ---------------------------------------------------------------------------
// Stack collapse helper
// ---------------------------------------------------------------------------

/// Move `arity` values from the top of the stack down to `return_sp`,
/// then set SP to just past those values.
///
/// This is the core operation for block exit — it discards intermediate
/// values while preserving the block's result or loop params.
#[inline(always)]
fn collapse_stack(stack: &mut Stack, return_sp: u32, arity: u32) {
    let src = stack.sp() - arity * 8;
    for i in 0..arity {
        let val = stack.read_u64(src + i * 8);
        stack.write_u64(return_sp + i * 8, val);
    }
    stack.set_sp(return_sp + arity * 8);
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

pub(crate) fn execute(
    stack: &mut Stack,
    module: &Module,
    store: &mut Store,
    func_idx: u32,
    args: &[Value],
) -> Result<Vec<Value>, ExecError> {
    let func = module
        .get_func(func_idx)
        .ok_or_else(|| ExecError::NotFound(format!("function {func_idx} not found")))?;
    let func_type = &module.types[module.func_types[func_idx as usize] as usize];
    let result_types: Vec<wasmparser::ValType> = func_type.results().to_vec();

    // Push args as locals
    for arg in args {
        stack.push_u64(arg.to_bits());
    }

    let locals_sp: u32 = 0;

    // Zero-initialize extra locals
    for _ in func_type.params().len()..func.locals.len() {
        stack.push_u64(0);
    }

    let return_sp = stack.sp();

    // Interpret the function body (block 0 is the implicit function block)
    let flow = interpret_block(stack, module, store, func, locals_sp, 0, func.body.len(), 0)?;

    match flow {
        Flow::Normal | Flow::Branch(0) | Flow::Return => {
            collapse_stack(stack, return_sp, func.blocks[0].results_arity);
        }
        Flow::Branch(_) => {
            return Err(ExecError::Trap("br beyond function boundary".into()));
        }
    }

    // Read results from the stack
    let mut results = Vec::with_capacity(result_types.len());
    let base = stack.sp() - result_types.len() as u32 * 8;
    for (i, &ty) in result_types.iter().enumerate() {
        results.push(Value::from_bits(stack.read_u64(base + i as u32 * 8), ty));
    }
    Ok(results)
}

// ---------------------------------------------------------------------------
// Recursive interpreter
// ---------------------------------------------------------------------------

/// Interpret instructions from `start_pc` to `end_pc` (exclusive).
///
/// Each block/loop/if recurses into a new `interpret_block` call.
/// `br` returns `Flow::Branch(depth)` which propagates up through
/// the recursion until the target block handles it.
fn interpret_block(
    stack: &mut Stack,
    module: &Module,
    store: &mut Store,
    func: &Func,
    locals_sp: u32,
    start_pc: usize,
    end_pc: usize,
    call_depth: usize,
) -> Result<Flow, ExecError> {
    let body = &func.body;
    let blocks = &func.blocks;
    let br_tables = &func.br_tables;
    let mut pc = start_pc;

    while pc < end_pc {
        let op = body[pc];
        pc += 1;

        match op.code {
            OP_UNREACHABLE => return Err(ExecError::Trap("unreachable".into())),
            OP_NOP => {}

            // ---- Control flow (recursive) ----

            OP_BLOCK => {
                let block = &blocks[op.imm_u32() as usize];
                let return_sp = stack.sp();
                let flow = interpret_block(
                    stack, module, store, func, locals_sp,
                    pc, block.end_pc as usize, call_depth,
                )?;
                pc = block.end_pc as usize + 1;
                match flow {
                    Flow::Normal | Flow::Branch(0) => {
                        collapse_stack(stack, return_sp, block.results_arity);
                    }
                    Flow::Branch(n) => return Ok(Flow::Branch(n - 1)),
                    Flow::Return => return Ok(Flow::Return),
                }
            }
            OP_LOOP => {
                let block = &blocks[op.imm_u32() as usize];
                let return_sp = stack.sp();
                loop {
                    let flow = interpret_block(
                        stack, module, store, func, locals_sp,
                        pc, block.end_pc as usize, call_depth,
                    )?;
                    match flow {
                        Flow::Normal => {
                            collapse_stack(stack, return_sp, block.results_arity);
                            break;
                        }
                        Flow::Branch(0) => {
                            collapse_stack(stack, return_sp, block.params_arity);
                            continue;
                        }
                        Flow::Branch(n) => return Ok(Flow::Branch(n - 1)),
                        Flow::Return => return Ok(Flow::Return),
                    }
                }
                pc = block.end_pc as usize + 1;
            }
            OP_IF => {
                let cond = pop_i32(stack);
                let block = &blocks[op.imm_u32() as usize];
                let return_sp = stack.sp();
                let flow = if cond != 0 {
                    interpret_block(
                        stack, module, store, func, locals_sp,
                        pc, block.end_pc as usize, call_depth,
                    )?
                } else {
                    Flow::Normal
                };
                pc = block.end_pc as usize + 1;
                match flow {
                    Flow::Normal | Flow::Branch(0) => {
                        collapse_stack(stack, return_sp, block.results_arity);
                    }
                    Flow::Branch(n) => return Ok(Flow::Branch(n - 1)),
                    Flow::Return => return Ok(Flow::Return),
                }
            }
            OP_IF_ELSE => {
                let cond = pop_i32(stack);
                let block = &blocks[op.imm_u32() as usize];
                let return_sp = stack.sp();
                let flow = if cond != 0 {
                    interpret_block(
                        stack, module, store, func, locals_sp,
                        pc, block.else_pc as usize, call_depth,
                    )?
                } else {
                    interpret_block(
                        stack, module, store, func, locals_sp,
                        block.else_pc as usize + 1, block.end_pc as usize, call_depth,
                    )?
                };
                pc = block.end_pc as usize + 1;
                match flow {
                    Flow::Normal | Flow::Branch(0) => {
                        collapse_stack(stack, return_sp, block.results_arity);
                    }
                    Flow::Branch(n) => return Ok(Flow::Branch(n - 1)),
                    Flow::Return => return Ok(Flow::Return),
                }
            }
            // OP_ELSE and OP_END are block delimiters — the recursive
            // structure means we never execute them directly. If we hit
            // OP_ELSE, it means the true branch fell through to else;
            // just stop this block (the parent handles it).
            OP_ELSE | OP_END => {
                return Ok(Flow::Normal);
            }
            OP_BR => {
                return Ok(Flow::Branch(op.imm_u32()));
            }
            OP_BR_IF => {
                let cond = pop_i32(stack);
                if cond != 0 {
                    return Ok(Flow::Branch(op.imm_u32()));
                }
            }
            OP_BR_TABLE => {
                let (ref targets, default) = br_tables[op.imm as usize];
                let idx = pop_i32(stack) as usize;
                let depth = if idx < targets.len() {
                    targets[idx]
                } else {
                    default
                };
                return Ok(Flow::Branch(depth));
            }
            OP_RETURN => {
                return Ok(Flow::Return);
            }

            // ---- Calls ----

            OP_CALL => {
                let idx = op.imm_u32();
                call_func(stack, module, store, idx, call_depth)?;
            }
            OP_CALL_INDIRECT => {
                let ci_type_idx = op.imm_hi();
                let elem_idx = pop_i32(stack) as u32;
                let target_func_idx =
                    resolve_table_element(store, op.imm_lo(), elem_idx)?;
                let ci_type = module.types.get(ci_type_idx as usize).ok_or_else(|| {
                    ExecError::Trap(format!("type index {} out of bounds", ci_type_idx))
                })?;

                if target_func_idx >= EXTERN_FUNC_BASE {
                    let extern_idx = (target_func_idx - EXTERN_FUNC_BASE) as usize;
                    let extern_fn = store.extern_funcs.get(extern_idx).ok_or_else(|| {
                        ExecError::Trap(format!("unresolved extern function {target_func_idx}"))
                    })?;
                    call_host(stack, extern_fn.as_ref(), ci_type.params(), &mut store.memory)?;
                } else if module.is_import(target_func_idx) {
                    check_indirect_type(module, target_func_idx, ci_type)?;
                    let host_fn = store.host_funcs.get(target_func_idx as usize).ok_or_else(|| {
                        ExecError::Trap(format!("unresolved import function {target_func_idx}"))
                    })?;
                    call_host(stack, host_fn.as_ref(), ci_type.params(), &mut store.memory)?;
                } else {
                    let callee_type_idx = module.func_types[target_func_idx as usize];
                    let callee_type = &module.types[callee_type_idx as usize];
                    if *callee_type != *ci_type {
                        return Err(ExecError::Trap("indirect call type mismatch".into()));
                    }
                    call_func(stack, module, store, target_func_idx, call_depth)?;
                }
            }

            // ---- Stack operations ----

            OP_DROP => { pop_raw(stack); }
            OP_SELECT => {
                let cond = pop_i32(stack);
                let b = pop_raw(stack);
                let a = pop_raw(stack);
                stack.push_u64(if cond != 0 { a } else { b });
            }

            // ---- Superinstructions ----

            OP_LOCAL_GET_I32_CONST => {
                let idx = op.imm_hi() as u32;
                let val = op.imm_lo();
                let v = stack.read_u64(locals_sp + idx * 8);
                stack.push_u64(v);
                stack.push_u64(val as u64);
            }
            OP_LOCAL_GET_LOCAL_GET => {
                let a = op.imm_hi() as u32;
                let b = op.imm_lo() as u32;
                let va = stack.read_u64(locals_sp + a * 8);
                let vb = stack.read_u64(locals_sp + b * 8);
                stack.push_u64(va);
                stack.push_u64(vb);
            }

            // ---- Locals / Globals ----

            OP_LOCAL_GET => {
                let v = stack.read_u64(locals_sp + op.imm as u32 * 8);
                stack.push_u64(v);
            }
            OP_LOCAL_SET => {
                let v = pop_raw(stack);
                stack.write_u64(locals_sp + op.imm as u32 * 8, v);
            }
            OP_LOCAL_TEE => {
                let v = stack.read_u64(stack.sp() - 8);
                stack.write_u64(locals_sp + op.imm as u32 * 8, v);
            }
            OP_GLOBAL_GET => {
                let g = store.globals.get(op.imm as usize).ok_or_else(|| {
                    ExecError::Trap(format!("global index {} out of bounds", op.imm))
                })?;
                stack.push_u64(g.to_bits());
            }
            OP_GLOBAL_SET => {
                let bits = pop_raw(stack);
                let idx = op.imm as usize;
                let g = store.globals.get(idx).ok_or_else(|| {
                    ExecError::Trap(format!("global index {} out of bounds", idx))
                })?;
                store.globals[idx] = coerce_bits_to_global(bits, g)?;
            }

            // ---- Memory loads ----

            OP_I32_LOAD => mem_load!(stack, store, &op.imm, 4, |b: [u8; 4]| {
                i32::from_le_bytes(b) as u32 as u64
            }),
            OP_I64_LOAD => mem_load!(stack, store, &op.imm, 8, |b: [u8; 8]| {
                i64::from_le_bytes(b) as u64
            }),
            OP_F32_LOAD => mem_load!(stack, store, &op.imm, 4, |b: [u8; 4]| {
                u32::from_le_bytes(b) as u64
            }),
            OP_F64_LOAD => mem_load!(stack, store, &op.imm, 8, |b: [u8; 8]| {
                u64::from_le_bytes(b)
            }),
            OP_I32_LOAD8_S => mem_load!(stack, store, &op.imm, 1, |b: [u8; 1]| {
                (b[0] as i8 as i32) as u32 as u64
            }),
            OP_I32_LOAD8_U => mem_load!(stack, store, &op.imm, 1, |b: [u8; 1]| {
                b[0] as u64
            }),
            OP_I32_LOAD16_S => mem_load!(stack, store, &op.imm, 2, |b: [u8; 2]| {
                (i16::from_le_bytes(b) as i32) as u32 as u64
            }),
            OP_I32_LOAD16_U => mem_load!(stack, store, &op.imm, 2, |b: [u8; 2]| {
                u16::from_le_bytes(b) as u64
            }),
            OP_I64_LOAD8_S => mem_load!(stack, store, &op.imm, 1, |b: [u8; 1]| {
                (b[0] as i8 as i64) as u64
            }),
            OP_I64_LOAD8_U => mem_load!(stack, store, &op.imm, 1, |b: [u8; 1]| {
                b[0] as u64
            }),
            OP_I64_LOAD16_S => mem_load!(stack, store, &op.imm, 2, |b: [u8; 2]| {
                (i16::from_le_bytes(b) as i64) as u64
            }),
            OP_I64_LOAD16_U => mem_load!(stack, store, &op.imm, 2, |b: [u8; 2]| {
                u16::from_le_bytes(b) as u64
            }),
            OP_I64_LOAD32_S => mem_load!(stack, store, &op.imm, 4, |b: [u8; 4]| {
                (i32::from_le_bytes(b) as i64) as u64
            }),
            OP_I64_LOAD32_U => mem_load!(stack, store, &op.imm, 4, |b: [u8; 4]| {
                u32::from_le_bytes(b) as u64
            }),

            // ---- Memory stores ----

            OP_I32_STORE => mem_store!(stack, store, &op.imm, pop_i32, |v: i32| v.to_le_bytes()),
            OP_I64_STORE => mem_store!(stack, store, &op.imm, pop_i64, |v: i64| v.to_le_bytes()),
            OP_F32_STORE => mem_store!(stack, store, &op.imm, pop_f32, |v: f32| v.to_le_bytes()),
            OP_F64_STORE => mem_store!(stack, store, &op.imm, pop_f64, |v: f64| v.to_le_bytes()),
            OP_I32_STORE8 => mem_store!(stack, store, &op.imm, pop_i32, |v: i32| (v as u8).to_le_bytes()),
            OP_I32_STORE16 => mem_store!(stack, store, &op.imm, pop_i32, |v: i32| (v as u16).to_le_bytes()),
            OP_I64_STORE8 => mem_store!(stack, store, &op.imm, pop_i64, |v: i64| (v as u8).to_le_bytes()),
            OP_I64_STORE16 => mem_store!(stack, store, &op.imm, pop_i64, |v: i64| (v as u16).to_le_bytes()),
            OP_I64_STORE32 => mem_store!(stack, store, &op.imm, pop_i64, |v: i64| (v as u32).to_le_bytes()),

            OP_MEMORY_SIZE => push_i32!(stack, store.memory_size()),
            OP_MEMORY_GROW => {
                let pages = pop_i32(stack);
                push_i32!(stack, store.memory_grow(pages as u32));
            }

            // ---- Constants ----

            OP_I32_CONST => stack.push_u64(op.imm),
            OP_I64_CONST => stack.push_u64(op.imm),
            OP_F32_CONST => stack.push_u64(op.imm),
            OP_F64_CONST => stack.push_u64(op.imm),

            // ---- i32 comparison ----

            OP_I32_EQZ => unop_i32!(stack, |a: i32| if a == 0 { 1i32 } else { 0i32 }),
            OP_I32_EQ => cmpop_i32!(stack, |a: i32, b: i32| a == b),
            OP_I32_NE => cmpop_i32!(stack, |a: i32, b: i32| a != b),
            OP_I32_LT_S => cmpop_i32!(stack, |a: i32, b: i32| a < b),
            OP_I32_LT_U => cmpop_i32!(stack, |a: i32, b: i32| (a as u32) < (b as u32)),
            OP_I32_GT_S => cmpop_i32!(stack, |a: i32, b: i32| a > b),
            OP_I32_GT_U => cmpop_i32!(stack, |a: i32, b: i32| (a as u32) > (b as u32)),
            OP_I32_LE_S => cmpop_i32!(stack, |a: i32, b: i32| a <= b),
            OP_I32_LE_U => cmpop_i32!(stack, |a: i32, b: i32| (a as u32) <= (b as u32)),
            OP_I32_GE_S => cmpop_i32!(stack, |a: i32, b: i32| a >= b),
            OP_I32_GE_U => cmpop_i32!(stack, |a: i32, b: i32| (a as u32) >= (b as u32)),

            // ---- i32 arithmetic ----

            OP_I32_CLZ => unop_i32!(stack, |a: i32| a.leading_zeros() as i32),
            OP_I32_CTZ => unop_i32!(stack, |a: i32| a.trailing_zeros() as i32),
            OP_I32_POPCNT => unop_i32!(stack, |a: i32| a.count_ones() as i32),
            OP_I32_ADD => binop_i32!(stack, |a: i32, b: i32| a.wrapping_add(b)),
            OP_I32_SUB => binop_i32!(stack, |a: i32, b: i32| a.wrapping_sub(b)),
            OP_I32_MUL => binop_i32!(stack, |a: i32, b: i32| a.wrapping_mul(b)),
            OP_I32_DIV_S => div_s!(stack, pop_i32, i32),
            OP_I32_DIV_U => div_u_i32!(stack),
            OP_I32_REM_S => rem_s_i32!(stack),
            OP_I32_REM_U => rem_u_i32!(stack),
            OP_I32_AND => binop_i32!(stack, |a: i32, b: i32| a & b),
            OP_I32_OR => binop_i32!(stack, |a: i32, b: i32| a | b),
            OP_I32_XOR => binop_i32!(stack, |a: i32, b: i32| a ^ b),
            OP_I32_SHL => binop_i32!(stack, |a: i32, b: i32| a.wrapping_shl(b as u32)),
            OP_I32_SHR_S => binop_i32!(stack, |a: i32, b: i32| a.wrapping_shr(b as u32)),
            OP_I32_SHR_U => {
                let b = pop_i32(stack) as u32;
                let a = pop_i32(stack) as u32;
                push_i32!(stack, a.wrapping_shr(b) as i32);
            }
            OP_I32_ROTL => binop_i32!(stack, |a: i32, b: i32| a.rotate_left(b as u32)),
            OP_I32_ROTR => binop_i32!(stack, |a: i32, b: i32| a.rotate_right(b as u32)),

            // ---- i64 comparison ----

            OP_I64_EQZ => {
                let a = pop_i64(stack);
                push_i32!(stack, if a == 0 { 1i32 } else { 0i32 });
            }
            OP_I64_EQ => cmpop_i64!(stack, |a: i64, b: i64| a == b),
            OP_I64_NE => cmpop_i64!(stack, |a: i64, b: i64| a != b),
            OP_I64_LT_S => cmpop_i64!(stack, |a: i64, b: i64| a < b),
            OP_I64_LT_U => cmpop_i64!(stack, |a: i64, b: i64| (a as u64) < (b as u64)),
            OP_I64_GT_S => cmpop_i64!(stack, |a: i64, b: i64| a > b),
            OP_I64_GT_U => cmpop_i64!(stack, |a: i64, b: i64| (a as u64) > (b as u64)),
            OP_I64_LE_S => cmpop_i64!(stack, |a: i64, b: i64| a <= b),
            OP_I64_LE_U => cmpop_i64!(stack, |a: i64, b: i64| (a as u64) <= (b as u64)),
            OP_I64_GE_S => cmpop_i64!(stack, |a: i64, b: i64| a >= b),
            OP_I64_GE_U => cmpop_i64!(stack, |a: i64, b: i64| (a as u64) >= (b as u64)),

            // ---- i64 arithmetic ----

            OP_I64_CLZ => unop_i64!(stack, |a: i64| a.leading_zeros() as i64),
            OP_I64_CTZ => unop_i64!(stack, |a: i64| a.trailing_zeros() as i64),
            OP_I64_POPCNT => unop_i64!(stack, |a: i64| a.count_ones() as i64),
            OP_I64_ADD => binop_i64!(stack, |a: i64, b: i64| a.wrapping_add(b)),
            OP_I64_SUB => binop_i64!(stack, |a: i64, b: i64| a.wrapping_sub(b)),
            OP_I64_MUL => binop_i64!(stack, |a: i64, b: i64| a.wrapping_mul(b)),
            OP_I64_DIV_S => div_s_i64!(stack),
            OP_I64_DIV_U => div_u_i64!(stack),
            OP_I64_REM_S => rem_s_i64!(stack),
            OP_I64_REM_U => rem_u_i64!(stack),
            OP_I64_AND => binop_i64!(stack, |a: i64, b: i64| a & b),
            OP_I64_OR => binop_i64!(stack, |a: i64, b: i64| a | b),
            OP_I64_XOR => binop_i64!(stack, |a: i64, b: i64| a ^ b),
            OP_I64_SHL => binop_i64!(stack, |a: i64, b: i64| a.wrapping_shl(b as u32)),
            OP_I64_SHR_S => binop_i64!(stack, |a: i64, b: i64| a.wrapping_shr(b as u32)),
            OP_I64_SHR_U => {
                let b = pop_i64(stack) as u64;
                let a = pop_i64(stack) as u64;
                push_i64!(stack, a.wrapping_shr(b as u32) as i64);
            }
            OP_I64_ROTL => binop_i64!(stack, |a: i64, b: i64| a.rotate_left(b as u32)),
            OP_I64_ROTR => binop_i64!(stack, |a: i64, b: i64| a.rotate_right(b as u32)),

            // ---- Conversions ----

            OP_I32_WRAP_I64 => { let a = pop_i64(stack); push_i32!(stack, a as i32); }
            OP_I64_EXTEND_I32_S => { let a = pop_i32(stack); push_i64!(stack, a as i64); }
            OP_I64_EXTEND_I32_U => { let a = pop_i32(stack); push_i64!(stack, (a as u32) as i64); }
            OP_I32_EXTEND8_S => unop_i32!(stack, |a: i32| a as i8 as i32),
            OP_I32_EXTEND16_S => unop_i32!(stack, |a: i32| a as i16 as i32),
            OP_I64_EXTEND8_S => unop_i64!(stack, |a: i64| a as i8 as i64),
            OP_I64_EXTEND16_S => unop_i64!(stack, |a: i64| a as i16 as i64),
            OP_I64_EXTEND32_S => unop_i64!(stack, |a: i64| a as i32 as i64),

            OP_I32_REINTERPRET_F32 => { let a = pop_f32(stack); push_i32!(stack, a.to_bits() as i32); }
            OP_I64_REINTERPRET_F64 => { let a = pop_f64(stack); push_i64!(stack, a.to_bits() as i64); }
            OP_F32_REINTERPRET_I32 => { let a = pop_i32(stack); push_f32!(stack, f32::from_bits(a as u32)); }
            OP_F64_REINTERPRET_I64 => { let a = pop_i64(stack); push_f64!(stack, f64::from_bits(a as u64)); }

            // ---- f32 comparison ----

            OP_F32_EQ => cmpop_f32!(stack, |a: f32, b: f32| a == b),
            OP_F32_NE => cmpop_f32!(stack, |a: f32, b: f32| a != b),
            OP_F32_LT => cmpop_f32!(stack, |a: f32, b: f32| a < b),
            OP_F32_GT => cmpop_f32!(stack, |a: f32, b: f32| a > b),
            OP_F32_LE => cmpop_f32!(stack, |a: f32, b: f32| a <= b),
            OP_F32_GE => cmpop_f32!(stack, |a: f32, b: f32| a >= b),

            OP_F64_EQ => cmpop_f64!(stack, |a: f64, b: f64| a == b),
            OP_F64_NE => cmpop_f64!(stack, |a: f64, b: f64| a != b),
            OP_F64_LT => cmpop_f64!(stack, |a: f64, b: f64| a < b),
            OP_F64_GT => cmpop_f64!(stack, |a: f64, b: f64| a > b),
            OP_F64_LE => cmpop_f64!(stack, |a: f64, b: f64| a <= b),
            OP_F64_GE => cmpop_f64!(stack, |a: f64, b: f64| a >= b),

            // ---- f32 arithmetic ----

            OP_F32_ABS => unop_f32!(stack, |a: f32| a.abs()),
            OP_F32_NEG => unop_f32!(stack, |a: f32| -a),
            OP_F32_CEIL => unop_f32!(stack, |a: f32| a.ceil()),
            OP_F32_FLOOR => unop_f32!(stack, |a: f32| a.floor()),
            OP_F32_TRUNC => unop_f32!(stack, |a: f32| a.trunc()),
            OP_F32_NEAREST => unop_f32!(stack, wasm_nearest),
            OP_F32_SQRT => unop_f32!(stack, |a: f32| a.sqrt()),
            OP_F32_ADD => binop_f32!(stack, |a: f32, b: f32| a + b),
            OP_F32_SUB => binop_f32!(stack, |a: f32, b: f32| a - b),
            OP_F32_MUL => binop_f32!(stack, |a: f32, b: f32| a * b),
            OP_F32_DIV => binop_f32!(stack, |a: f32, b: f32| a / b),
            OP_F32_MIN => binop_f32!(stack, wasm_min),
            OP_F32_MAX => binop_f32!(stack, wasm_max),
            OP_F32_COPYSIGN => binop_f32!(stack, |a: f32, b: f32| a.copysign(b)),

            // ---- f64 arithmetic ----

            OP_F64_ABS => unop_f64!(stack, |a: f64| a.abs()),
            OP_F64_NEG => unop_f64!(stack, |a: f64| -a),
            OP_F64_CEIL => unop_f64!(stack, |a: f64| a.ceil()),
            OP_F64_FLOOR => unop_f64!(stack, |a: f64| a.floor()),
            OP_F64_TRUNC => unop_f64!(stack, |a: f64| a.trunc()),
            OP_F64_NEAREST => unop_f64!(stack, wasm_nearest),
            OP_F64_SQRT => unop_f64!(stack, |a: f64| a.sqrt()),
            OP_F64_ADD => binop_f64!(stack, |a: f64, b: f64| a + b),
            OP_F64_SUB => binop_f64!(stack, |a: f64, b: f64| a - b),
            OP_F64_MUL => binop_f64!(stack, |a: f64, b: f64| a * b),
            OP_F64_DIV => binop_f64!(stack, |a: f64, b: f64| a / b),
            OP_F64_MIN => binop_f64!(stack, wasm_min),
            OP_F64_MAX => binop_f64!(stack, wasm_max),
            OP_F64_COPYSIGN => binop_f64!(stack, |a: f64, b: f64| a.copysign(b)),

            // ---- Float-int conversions ----

            OP_I32_TRUNC_F32_S => trunc_op!(stack, pop_f32, push_i32, i32, 2147483648.0_f32, -2147483648.0_f32),
            OP_I32_TRUNC_F32_U => trunc_op_u!(stack, pop_f32, push_i32, u32, i32, 4294967296.0_f32),
            OP_I32_TRUNC_F64_S => trunc_op!(stack, pop_f64, push_i32, i32, 2147483648.0_f64, -2147483648.0_f64),
            OP_I32_TRUNC_F64_U => trunc_op_u!(stack, pop_f64, push_i32, u32, i32, 4294967296.0_f64),
            OP_I64_TRUNC_F32_S => trunc_op!(stack, pop_f32, push_i64, i64, 9223372036854775808.0_f32, -9223372036854775808.0_f32),
            OP_I64_TRUNC_F32_U => trunc_op_u!(stack, pop_f32, push_i64, u64, i64, 18446744073709551616.0_f32),
            OP_I64_TRUNC_F64_S => trunc_op!(stack, pop_f64, push_i64, i64, 9223372036854775808.0_f64, -9223372036854775808.0_f64),
            OP_I64_TRUNC_F64_U => trunc_op_u!(stack, pop_f64, push_i64, u64, i64, 18446744073709551616.0_f64),

            OP_I32_TRUNC_SAT_F32_S => trunc_sat_s!(stack, pop_f32, push_i32, i32, 2147483648.0_f32, -2147483648.0_f32),
            OP_I32_TRUNC_SAT_F32_U => trunc_sat_u!(stack, pop_f32, push_i32, u32, i32, 4294967296.0_f32),
            OP_I32_TRUNC_SAT_F64_S => trunc_sat_s!(stack, pop_f64, push_i32, i32, 2147483648.0_f64, -2147483648.0_f64),
            OP_I32_TRUNC_SAT_F64_U => trunc_sat_u!(stack, pop_f64, push_i32, u32, i32, 4294967296.0_f64),
            OP_I64_TRUNC_SAT_F32_S => trunc_sat_s!(stack, pop_f32, push_i64, i64, 9223372036854775808.0_f32, -9223372036854775808.0_f32),
            OP_I64_TRUNC_SAT_F32_U => trunc_sat_u!(stack, pop_f32, push_i64, u64, i64, 18446744073709551616.0_f32),
            OP_I64_TRUNC_SAT_F64_S => trunc_sat_s!(stack, pop_f64, push_i64, i64, 9223372036854775808.0_f64, -9223372036854775808.0_f64),
            OP_I64_TRUNC_SAT_F64_U => trunc_sat_u!(stack, pop_f64, push_i64, u64, i64, 18446744073709551616.0_f64),

            OP_F32_CONVERT_I32_S => { let a = pop_i32(stack); push_f32!(stack, a as f32); }
            OP_F32_CONVERT_I32_U => { let a = pop_i32(stack); push_f32!(stack, (a as u32) as f32); }
            OP_F32_CONVERT_I64_S => { let a = pop_i64(stack); push_f32!(stack, a as f32); }
            OP_F32_CONVERT_I64_U => { let a = pop_i64(stack); push_f32!(stack, (a as u64) as f32); }
            OP_F32_DEMOTE_F64 => { let a = pop_f64(stack); push_f32!(stack, a as f32); }
            OP_F64_CONVERT_I32_S => { let a = pop_i32(stack); push_f64!(stack, a as f64); }
            OP_F64_CONVERT_I32_U => { let a = pop_i32(stack); push_f64!(stack, (a as u32) as f64); }
            OP_F64_CONVERT_I64_S => { let a = pop_i64(stack); push_f64!(stack, a as f64); }
            OP_F64_CONVERT_I64_U => { let a = pop_i64(stack); push_f64!(stack, (a as u64) as f64); }
            OP_F64_PROMOTE_F32 => { let a = pop_f32(stack); push_f64!(stack, a as f64); }

            // ---- Table / Memory bulk ops ----

            OP_TABLE_INIT => {
                let n = pop_i32(stack) as u32;
                let s = pop_i32(stack) as u32;
                let d = pop_i32(stack) as u32;
                execute_table_init(store, op.imm_hi() as usize, op.imm_lo() as usize, d, s, n)?;
            }
            OP_ELEM_DROP => {
                let elem_idx = op.imm as usize;
                if elem_idx < store.elem_segments.len() {
                    store.elem_segments[elem_idx] = None;
                }
            }
            OP_REF_FUNC => stack.push_u64(op.imm_u32() as u64),
            OP_REF_NULL => stack.push_u64(u64::MAX),
            OP_REF_IS_NULL => {
                let val = pop_raw(stack);
                push_i32!(stack, if val == u64::MAX { 1i32 } else { 0i32 });
            }
            OP_MEMORY_INIT => {
                let n = pop_i32(stack) as u32;
                let s = pop_i32(stack) as u32;
                let d = pop_i32(stack) as u32;
                execute_memory_init(store, op.imm as usize, d, s, n)?;
            }
            OP_DATA_DROP => {
                let seg_idx = op.imm as usize;
                if seg_idx < store.data_segments.len() {
                    store.data_segments[seg_idx] = None;
                }
            }
            OP_MEMORY_COPY => {
                let n = pop_i32(stack) as u32;
                let s = pop_i32(stack) as u32;
                let d = pop_i32(stack) as u32;
                if s as u64 + n as u64 > store.memory.len() as u64
                    || d as u64 + n as u64 > store.memory.len() as u64
                {
                    return Err(ExecError::oob_memory());
                }
                store.memory.copy_within(s as usize..(s + n) as usize, d as usize);
            }
            OP_MEMORY_FILL => {
                let n = pop_i32(stack) as u32;
                let val = pop_i32(stack) as u8;
                let d = pop_i32(stack) as u32;
                if d as u64 + n as u64 > store.memory.len() as u64 {
                    return Err(ExecError::oob_memory());
                }
                store.memory[d as usize..(d + n) as usize].fill(val);
            }
            OP_TABLE_GET => {
                let idx = pop_i32(stack) as u32;
                let table_idx = op.imm as usize;
                let shared_table = store.tables.get(table_idx)
                    .ok_or_else(|| ExecError::Trap("undefined table".into()))?;
                let table = shared_table.borrow();
                if idx as usize >= table.len() {
                    return Err(ExecError::oob_table());
                }
                match table[idx as usize] {
                    Some(func_idx) => stack.push_u64(func_idx as u64),
                    None => stack.push_u64(u64::MAX),
                }
            }
            OP_TABLE_SET => {
                let val = pop_raw(stack);
                let idx = pop_i32(stack) as u32;
                let table_idx = op.imm as usize;
                let shared_table = store.tables.get(table_idx)
                    .ok_or_else(|| ExecError::Trap("undefined table".into()))?;
                let mut table = shared_table.borrow_mut();
                if idx as usize >= table.len() {
                    return Err(ExecError::oob_table());
                }
                table[idx as usize] = if val == u64::MAX { None } else { Some(val as u32) };
            }
            OP_TABLE_SIZE => {
                let table_idx = op.imm as usize;
                let shared_table = store.tables.get(table_idx)
                    .ok_or_else(|| ExecError::Trap("undefined table".into()))?;
                push_i32!(stack, shared_table.borrow().len() as i32);
            }
            OP_TABLE_GROW => {
                let n = pop_i32(stack) as u32;
                let init_val = pop_raw(stack);
                let table_idx = op.imm as usize;
                let max = store.table_defs.get(table_idx).and_then(|(_, max)| *max);
                let shared_table = store.tables.get(table_idx)
                    .ok_or_else(|| ExecError::Trap("undefined table".into()))?;
                let mut table = shared_table.borrow_mut();
                let old_size = table.len() as u32;
                let new_size = old_size as u64 + n as u64;
                if let Some(max) = max {
                    if new_size > max {
                        push_i32!(stack, -1i32);
                        continue;
                    }
                }
                if new_size > u32::MAX as u64 {
                    push_i32!(stack, -1i32);
                    continue;
                }
                let fill = if init_val == u64::MAX { None } else { Some(init_val as u32) };
                table.resize(new_size as usize, fill);
                push_i32!(stack, old_size as i32);
            }
            OP_TABLE_COPY => {
                let n = pop_i32(stack) as u32;
                let s = pop_i32(stack) as u32;
                let d = pop_i32(stack) as u32;
                execute_table_copy(store, op.imm_hi() as usize, op.imm_lo() as usize, d, s, n)?;
            }
            OP_TABLE_FILL => {
                let n = pop_i32(stack) as u32;
                let val = pop_raw(stack);
                let i = pop_i32(stack) as u32;
                let table_idx = op.imm as usize;
                let shared_table = store.tables.get(table_idx)
                    .ok_or_else(|| ExecError::Trap("undefined table".into()))?;
                let mut table = shared_table.borrow_mut();
                if i as u64 + n as u64 > table.len() as u64 {
                    return Err(ExecError::oob_table());
                }
                let fill = if val == u64::MAX { None } else { Some(val as u32) };
                for j in 0..n as usize {
                    table[i as usize + j] = fill;
                }
            }

            _ => {
                return Err(ExecError::Trap(format!("unimplemented opcode: {}", op.code)));
            }
        }
    }

    Ok(Flow::Normal)
}

// ---------------------------------------------------------------------------
// Function call helper
// ---------------------------------------------------------------------------

/// Call a WASM function (not an import). Sets up locals on the stack
/// and recursively interprets the callee's body.
fn call_func(
    stack: &mut Stack,
    module: &Module,
    store: &mut Store,
    func_idx: u32,
    call_depth: usize,
) -> Result<(), ExecError> {
    if module.is_import(func_idx) {
        let type_idx = module.func_types[func_idx as usize];
        let func_type = &module.types[type_idx as usize];
        let host_fn = store.host_funcs.get(func_idx as usize).ok_or_else(|| {
            ExecError::Trap(format!("unresolved import function {func_idx}"))
        })?;
        return call_host(stack, host_fn.as_ref(), func_type.params(), &mut store.memory);
    }

    if call_depth >= 1024 {
        return Err(ExecError::Trap("call stack exhausted".into()));
    }

    let callee = module.get_func(func_idx)
        .ok_or_else(|| ExecError::Trap(format!("function {func_idx} not found")))?;
    let callee_type = &module.types[module.func_types[func_idx as usize] as usize];
    let param_count = callee_type.params().len();

    // Params are already on the stack — they become the first locals.
    let locals_sp = stack.sp() - param_count as u32 * 8;

    // Zero-initialize extra locals
    for _ in param_count..callee.locals.len() {
        stack.push_u64(0);
    }

    let return_sp = stack.sp();
    let result_count = callee_type.results().len() as u32;

    let flow = interpret_block(
        stack, module, store, callee, locals_sp,
        0, callee.body.len(), call_depth + 1,
    )?;

    match flow {
        Flow::Normal | Flow::Branch(0) | Flow::Return => {
            collapse_stack(stack, return_sp, result_count);
        }
        Flow::Branch(n) => {
            return Err(ExecError::Trap(format!("br depth {n} beyond function boundary")));
        }
    }

    // Move results down to where caller expects them (over the locals area)
    let result_bytes = result_count * 8;
    for i in 0..result_count {
        let val = stack.read_u64(return_sp + i * 8);
        stack.write_u64(locals_sp + i * 8, val);
    }
    stack.set_sp(locals_sp + result_bytes);

    Ok(())
}
