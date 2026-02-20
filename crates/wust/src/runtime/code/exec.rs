//! Main interpreter loop.
//!
//! Contains only the `execute` function — the giant opcode dispatch.
//! All supporting types, helpers, and entry points live in `program.rs`.

use super::helpers::{
    check_indirect_type, coerce_bits_to_global, execute_memory_init, execute_table_copy,
    execute_table_init, resolve_table_element,
};
use super::program::{
    CallFrame, ControlEntry, call_host, do_br, do_return, pop_f32, pop_f64, pop_i32, pop_i64,
    pop_raw,
};
use super::stack::Stack;
use crate::runtime::error::ExecError;
use crate::runtime::module::Module;
use crate::runtime::opcode::*;
use crate::runtime::store::{EXTERN_FUNC_BASE, Store};
use crate::runtime::value::{Value, wasm_max, wasm_min, wasm_nearest};

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
    let func_type_idx = module.func_types[func_idx as usize];
    let func_type = &module.types[func_type_idx as usize];
    let result_types: Vec<wasmparser::ValType> = func_type.results().to_vec();
    let param_count = func_type.params().len();

    // Push args onto stack as u64 values — these become the first N locals
    unsafe {
        for arg in args {
            stack.push_u64(arg.to_bits());
        }
    }

    let locals_sp: u32 = 0;

    // Zero-initialize extra locals
    let extra_locals = func.locals.len() - param_count;
    unsafe {
        for _ in 0..extra_locals {
            stack.push_u64(0);
        }
    }

    let mut controls: Vec<ControlEntry> = Vec::with_capacity(64);
    let mut call_frames: Vec<CallFrame> = Vec::with_capacity(64);

    controls.push(ControlEntry {
        return_sp: stack.sp(),
        target_pc: func.body.len(),
        arity: result_types.len(),
        is_loop: false,
    });

    let mut current_func_idx = func_idx;
    let mut current_locals_sp = locals_sp;
    let mut current_controls_start: usize = 0;
    let mut pc: usize = 0;

    let mut body: &[Op] = &func.body;
    let mut br_tables: &[(Vec<u32>, u32)] = &func.br_tables;

    unsafe {
        loop {
            if pc >= body.len() {
                if do_return(
                    stack,
                    &mut call_frames,
                    &mut controls,
                    module,
                    current_func_idx,
                    current_locals_sp,
                    current_controls_start,
                ) {
                    let mut results = Vec::with_capacity(result_types.len());
                    let base = stack.sp() - result_types.len() as u32 * 8;
                    for (i, &ty) in result_types.iter().enumerate() {
                        results.push(Value::from_bits(
                            stack.read_u64(base + i as u32 * 8),
                            ty,
                        ));
                    }
                    return Ok(results);
                }
                let caller = call_frames.pop().unwrap();
                let caller_func = module.get_func(caller.func_idx).unwrap();
                body = &caller_func.body;
                br_tables = &caller_func.br_tables;
                current_func_idx = caller.func_idx;
                pc = caller.pc;
                current_locals_sp = caller.locals_sp;
                current_controls_start = caller.controls_start;
                continue;
            }

            let op = body[pc];
            pc += 1;

            match op.code {
                OP_UNREACHABLE => {
                    return Err(ExecError::Trap("unreachable".into()));
                }
                OP_NOP => {}

                // ---- Control flow ----

                OP_BLOCK => {
                    let end_pc = op.imm_hi() as usize;
                    let arity = op.imm_lo() as usize;
                    controls.push(ControlEntry {
                        return_sp: stack.sp(),
                        target_pc: end_pc,
                        arity,
                        is_loop: false,
                    });
                }
                OP_LOOP => {
                    let arity = op.imm_u32() as usize;
                    controls.push(ControlEntry {
                        return_sp: stack.sp(),
                        target_pc: pc, // past the OP_LOOP itself to avoid re-pushing
                        arity,
                        is_loop: true,
                    });
                }
                OP_IF => {
                    let cond = pop_i32(stack);
                    let end_pc = op.imm_hi() as usize;
                    let arity = op.imm_lo() as usize;
                    controls.push(ControlEntry {
                        return_sp: stack.sp(),
                        target_pc: end_pc,
                        arity,
                        is_loop: false,
                    });
                    if cond == 0 {
                        pc = end_pc + 1;
                        controls.pop();
                    }
                }
                OP_IF_ELSE => {
                    let cond = pop_i32(stack);
                    let arity = (op.imm >> 56) as usize;
                    let end_pc = ((op.imm >> 28) & 0x0FFF_FFFF) as usize;
                    let else_pc = (op.imm & 0x0FFF_FFFF) as usize;
                    controls.push(ControlEntry {
                        return_sp: stack.sp(),
                        target_pc: end_pc,
                        arity,
                        is_loop: false,
                    });
                    if cond == 0 {
                        pc = else_pc + 1;
                    }
                }
                OP_ELSE => {
                    let label = controls.last().unwrap();
                    pc = label.target_pc + 1;
                    controls.pop();
                }
                OP_END => {
                    if controls.len() > current_controls_start + 1 {
                        controls.pop();
                    }
                }
                OP_BR => {
                    do_br(stack, &mut controls, op.imm_u32(), &mut pc);
                }
                OP_BR_IF => {
                    let cond = pop_i32(stack);
                    if cond != 0 {
                        do_br(stack, &mut controls, op.imm_u32(), &mut pc);
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
                    do_br(stack, &mut controls, depth, &mut pc);
                }
                OP_RETURN => {
                    if do_return(
                        stack,
                        &mut call_frames,
                        &mut controls,
                        module,
                        current_func_idx,
                        current_locals_sp,
                        current_controls_start,
                    ) {
                        let mut results = Vec::with_capacity(result_types.len());
                        let base = stack.sp() - result_types.len() as u32 * 8;
                        for (i, &ty) in result_types.iter().enumerate() {
                            results.push(Value::from_bits(
                                stack.read_u64(base + i as u32 * 8),
                                ty,
                            ));
                        }
                        return Ok(results);
                    }
                    let caller = call_frames.pop().unwrap();
                    let caller_func = module.get_func(caller.func_idx).unwrap();
                    body = &caller_func.body;
                    br_tables = &caller_func.br_tables;
                    current_func_idx = caller.func_idx;
                    pc = caller.pc;
                    current_locals_sp = caller.locals_sp;
                    current_controls_start = caller.controls_start;
                    continue;
                }

                // ---- Calls ----

                OP_CALL => {
                    let idx = op.imm_u32();

                    if module.is_import(idx) {
                        let type_idx = module.func_types[idx as usize];
                        let callee_type = &module.types[type_idx as usize];
                        let host_fn = store.host_funcs.get(idx as usize).ok_or_else(|| {
                            ExecError::Trap(format!("unresolved import function {idx}"))
                        })?;
                        call_host(
                            stack,
                            host_fn.as_ref(),
                            callee_type.params(),
                            &mut store.memory,
                        )?;
                    } else {
                        // TODO: replace with signal handler on guard page
                        if call_frames.len() >= 1024 {
                            return Err(ExecError::Trap("call stack exhausted".into()));
                        }

                        let callee = module.get_func(idx).ok_or_else(|| {
                            ExecError::Trap(format!("function {idx} not found"))
                        })?;
                        let callee_type_idx = module.func_types[idx as usize];
                        let callee_type = &module.types[callee_type_idx as usize];
                        let callee_param_count = callee_type.params().len();

                        let callee_locals_sp =
                            stack.sp() - callee_param_count as u32 * 8;

                        call_frames.push(CallFrame {
                            func_idx: current_func_idx,
                            pc,
                            locals_sp: current_locals_sp,
                            controls_start: current_controls_start,
                        });

                        let extra = callee.locals.len() - callee_param_count;
                        for _ in 0..extra {
                            stack.push_u64(0);
                        }

                        current_func_idx = idx;
                        pc = 0;
                        current_locals_sp = callee_locals_sp;
                        current_controls_start = controls.len();
                        body = &callee.body;
                        br_tables = &callee.br_tables;

                        controls.push(ControlEntry {
                            return_sp: stack.sp(),
                            target_pc: body.len(),
                            arity: callee_type.results().len(),
                            is_loop: false,
                        });
                    }
                }
                OP_CALL_INDIRECT => {
                    let ci_type_idx = op.imm_hi();
                    let elem_idx = pop_i32(stack) as u32;
                    let target_func_idx =
                        resolve_table_element(store, op.imm_lo(), elem_idx)?;
                    let ci_type = module.types.get(ci_type_idx as usize).ok_or_else(|| {
                        ExecError::Trap(format!(
                            "type index {} out of bounds",
                            ci_type_idx
                        ))
                    })?;

                    if target_func_idx >= EXTERN_FUNC_BASE {
                        let extern_idx = (target_func_idx - EXTERN_FUNC_BASE) as usize;
                        let extern_fn =
                            store.extern_funcs.get(extern_idx).ok_or_else(|| {
                                ExecError::Trap(format!(
                                    "unresolved extern function {target_func_idx}"
                                ))
                            })?;
                        call_host(
                            stack,
                            extern_fn.as_ref(),
                            ci_type.params(),
                            &mut store.memory,
                        )?;
                    } else if module.is_import(target_func_idx) {
                        check_indirect_type(module, target_func_idx, ci_type)?;
                        let host_fn =
                            store.host_funcs.get(target_func_idx as usize).ok_or_else(|| {
                                ExecError::Trap(format!(
                                    "unresolved import function {target_func_idx}"
                                ))
                            })?;
                        call_host(
                            stack,
                            host_fn.as_ref(),
                            ci_type.params(),
                            &mut store.memory,
                        )?;
                    } else {
                        // TODO: replace with signal handler on guard page
                        if call_frames.len() >= 1024 {
                            return Err(ExecError::Trap("call stack exhausted".into()));
                        }

                        let callee = module.get_func(target_func_idx).ok_or_else(|| {
                            ExecError::Trap(format!(
                                "function {target_func_idx} not found"
                            ))
                        })?;
                        let callee_type_idx = module.func_types[target_func_idx as usize];
                        let callee_type = &module.types[callee_type_idx as usize];
                        if *callee_type != *ci_type {
                            return Err(ExecError::Trap(
                                "indirect call type mismatch".into(),
                            ));
                        }
                        let callee_param_count = callee_type.params().len();
                        let callee_locals_sp =
                            stack.sp() - callee_param_count as u32 * 8;

                        call_frames.push(CallFrame {
                            func_idx: current_func_idx,
                            pc,
                            locals_sp: current_locals_sp,
                            controls_start: current_controls_start,
                        });

                        let extra = callee.locals.len() - callee_param_count;
                        for _ in 0..extra {
                            stack.push_u64(0);
                        }

                        current_func_idx = target_func_idx;
                        pc = 0;
                        current_locals_sp = callee_locals_sp;
                        current_controls_start = controls.len();
                        body = &callee.body;
                        br_tables = &callee.br_tables;

                        controls.push(ControlEntry {
                            return_sp: stack.sp(),
                            target_pc: body.len(),
                            arity: callee_type.results().len(),
                            is_loop: false,
                        });
                    }
                }

                // ---- Stack operations ----

                OP_DROP => {
                    pop_raw(stack);
                }
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
                    let v = stack.read_u64(current_locals_sp + idx * 8);
                    stack.push_u64(v);
                    stack.push_u64(val as u64);
                }
                OP_LOCAL_GET_LOCAL_GET => {
                    let a = op.imm_hi() as u32;
                    let b = op.imm_lo() as u32;
                    let va = stack.read_u64(current_locals_sp + a * 8);
                    let vb = stack.read_u64(current_locals_sp + b * 8);
                    stack.push_u64(va);
                    stack.push_u64(vb);
                }

                // ---- Locals / Globals ----

                OP_LOCAL_GET => {
                    let v = stack.read_u64(current_locals_sp + op.imm as u32 * 8);
                    stack.push_u64(v);
                }
                OP_LOCAL_SET => {
                    let v = pop_raw(stack);
                    stack.write_u64(current_locals_sp + op.imm as u32 * 8, v);
                }
                OP_LOCAL_TEE => {
                    let v = stack.read_u64(stack.sp() - 8);
                    stack.write_u64(current_locals_sp + op.imm as u32 * 8, v);
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

                OP_I32_STORE => {
                    mem_store!(stack, store, &op.imm, pop_i32, |v: i32| v.to_le_bytes())
                }
                OP_I64_STORE => {
                    mem_store!(stack, store, &op.imm, pop_i64, |v: i64| v.to_le_bytes())
                }
                OP_F32_STORE => {
                    mem_store!(stack, store, &op.imm, pop_f32, |v: f32| v.to_le_bytes())
                }
                OP_F64_STORE => {
                    mem_store!(stack, store, &op.imm, pop_f64, |v: f64| v.to_le_bytes())
                }
                OP_I32_STORE8 => {
                    mem_store!(stack, store, &op.imm, pop_i32, |v: i32| (v as u8)
                        .to_le_bytes())
                }
                OP_I32_STORE16 => {
                    mem_store!(stack, store, &op.imm, pop_i32, |v: i32| (v as u16)
                        .to_le_bytes())
                }
                OP_I64_STORE8 => {
                    mem_store!(stack, store, &op.imm, pop_i64, |v: i64| (v as u8)
                        .to_le_bytes())
                }
                OP_I64_STORE16 => {
                    mem_store!(stack, store, &op.imm, pop_i64, |v: i64| (v as u16)
                        .to_le_bytes())
                }
                OP_I64_STORE32 => {
                    mem_store!(stack, store, &op.imm, pop_i64, |v: i64| (v as u32)
                        .to_le_bytes())
                }

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
                OP_I32_SHR_S => {
                    binop_i32!(stack, |a: i32, b: i32| a.wrapping_shr(b as u32))
                }
                OP_I32_SHR_U => {
                    let b = pop_i32(stack) as u32;
                    let a = pop_i32(stack) as u32;
                    push_i32!(stack, a.wrapping_shr(b) as i32);
                }
                OP_I32_ROTL => binop_i32!(stack, |a: i32, b: i32| a.rotate_left(b as u32)),
                OP_I32_ROTR => {
                    binop_i32!(stack, |a: i32, b: i32| a.rotate_right(b as u32))
                }

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
                OP_I64_SHR_S => {
                    binop_i64!(stack, |a: i64, b: i64| a.wrapping_shr(b as u32))
                }
                OP_I64_SHR_U => {
                    let b = pop_i64(stack) as u64;
                    let a = pop_i64(stack) as u64;
                    push_i64!(stack, a.wrapping_shr(b as u32) as i64);
                }
                OP_I64_ROTL => binop_i64!(stack, |a: i64, b: i64| a.rotate_left(b as u32)),
                OP_I64_ROTR => {
                    binop_i64!(stack, |a: i64, b: i64| a.rotate_right(b as u32))
                }

                // ---- Conversions ----

                OP_I32_WRAP_I64 => {
                    let a = pop_i64(stack);
                    push_i32!(stack, a as i32);
                }
                OP_I64_EXTEND_I32_S => {
                    let a = pop_i32(stack);
                    push_i64!(stack, a as i64);
                }
                OP_I64_EXTEND_I32_U => {
                    let a = pop_i32(stack);
                    push_i64!(stack, (a as u32) as i64);
                }
                OP_I32_EXTEND8_S => unop_i32!(stack, |a: i32| a as i8 as i32),
                OP_I32_EXTEND16_S => unop_i32!(stack, |a: i32| a as i16 as i32),
                OP_I64_EXTEND8_S => unop_i64!(stack, |a: i64| a as i8 as i64),
                OP_I64_EXTEND16_S => unop_i64!(stack, |a: i64| a as i16 as i64),
                OP_I64_EXTEND32_S => unop_i64!(stack, |a: i64| a as i32 as i64),

                // Reinterpret
                OP_I32_REINTERPRET_F32 => {
                    let a = pop_f32(stack);
                    push_i32!(stack, a.to_bits() as i32);
                }
                OP_I64_REINTERPRET_F64 => {
                    let a = pop_f64(stack);
                    push_i64!(stack, a.to_bits() as i64);
                }
                OP_F32_REINTERPRET_I32 => {
                    let a = pop_i32(stack);
                    push_f32!(stack, f32::from_bits(a as u32));
                }
                OP_F64_REINTERPRET_I64 => {
                    let a = pop_i64(stack);
                    push_f64!(stack, f64::from_bits(a as u64));
                }

                // ---- f32 comparison ----

                OP_F32_EQ => cmpop_f32!(stack, |a: f32, b: f32| a == b),
                OP_F32_NE => cmpop_f32!(stack, |a: f32, b: f32| a != b),
                OP_F32_LT => cmpop_f32!(stack, |a: f32, b: f32| a < b),
                OP_F32_GT => cmpop_f32!(stack, |a: f32, b: f32| a > b),
                OP_F32_LE => cmpop_f32!(stack, |a: f32, b: f32| a <= b),
                OP_F32_GE => cmpop_f32!(stack, |a: f32, b: f32| a >= b),

                // ---- f64 comparison ----

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

                OP_I32_TRUNC_F32_S => trunc_op!(
                    stack, pop_f32, push_i32, i32,
                    2147483648.0_f32, -2147483648.0_f32
                ),
                OP_I32_TRUNC_F32_U => {
                    trunc_op_u!(stack, pop_f32, push_i32, u32, i32, 4294967296.0_f32)
                }
                OP_I32_TRUNC_F64_S => trunc_op!(
                    stack, pop_f64, push_i32, i32,
                    2147483648.0_f64, -2147483648.0_f64
                ),
                OP_I32_TRUNC_F64_U => {
                    trunc_op_u!(stack, pop_f64, push_i32, u32, i32, 4294967296.0_f64)
                }
                OP_I64_TRUNC_F32_S => trunc_op!(
                    stack, pop_f32, push_i64, i64,
                    9223372036854775808.0_f32, -9223372036854775808.0_f32
                ),
                OP_I64_TRUNC_F32_U => trunc_op_u!(
                    stack, pop_f32, push_i64, u64, i64,
                    18446744073709551616.0_f32
                ),
                OP_I64_TRUNC_F64_S => trunc_op!(
                    stack, pop_f64, push_i64, i64,
                    9223372036854775808.0_f64, -9223372036854775808.0_f64
                ),
                OP_I64_TRUNC_F64_U => trunc_op_u!(
                    stack, pop_f64, push_i64, u64, i64,
                    18446744073709551616.0_f64
                ),

                // ---- Saturating truncation ----

                OP_I32_TRUNC_SAT_F32_S => trunc_sat_s!(
                    stack, pop_f32, push_i32, i32,
                    2147483648.0_f32, -2147483648.0_f32
                ),
                OP_I32_TRUNC_SAT_F32_U => {
                    trunc_sat_u!(stack, pop_f32, push_i32, u32, i32, 4294967296.0_f32)
                }
                OP_I32_TRUNC_SAT_F64_S => trunc_sat_s!(
                    stack, pop_f64, push_i32, i32,
                    2147483648.0_f64, -2147483648.0_f64
                ),
                OP_I32_TRUNC_SAT_F64_U => {
                    trunc_sat_u!(stack, pop_f64, push_i32, u32, i32, 4294967296.0_f64)
                }
                OP_I64_TRUNC_SAT_F32_S => trunc_sat_s!(
                    stack, pop_f32, push_i64, i64,
                    9223372036854775808.0_f32, -9223372036854775808.0_f32
                ),
                OP_I64_TRUNC_SAT_F32_U => trunc_sat_u!(
                    stack, pop_f32, push_i64, u64, i64,
                    18446744073709551616.0_f32
                ),
                OP_I64_TRUNC_SAT_F64_S => trunc_sat_s!(
                    stack, pop_f64, push_i64, i64,
                    9223372036854775808.0_f64, -9223372036854775808.0_f64
                ),
                OP_I64_TRUNC_SAT_F64_U => trunc_sat_u!(
                    stack, pop_f64, push_i64, u64, i64,
                    18446744073709551616.0_f64
                ),

                OP_F32_CONVERT_I32_S => {
                    let a = pop_i32(stack);
                    push_f32!(stack, a as f32);
                }
                OP_F32_CONVERT_I32_U => {
                    let a = pop_i32(stack);
                    push_f32!(stack, (a as u32) as f32);
                }
                OP_F32_CONVERT_I64_S => {
                    let a = pop_i64(stack);
                    push_f32!(stack, a as f32);
                }
                OP_F32_CONVERT_I64_U => {
                    let a = pop_i64(stack);
                    push_f32!(stack, (a as u64) as f32);
                }
                OP_F32_DEMOTE_F64 => {
                    let a = pop_f64(stack);
                    push_f32!(stack, a as f32);
                }
                OP_F64_CONVERT_I32_S => {
                    let a = pop_i32(stack);
                    push_f64!(stack, a as f64);
                }
                OP_F64_CONVERT_I32_U => {
                    let a = pop_i32(stack);
                    push_f64!(stack, (a as u32) as f64);
                }
                OP_F64_CONVERT_I64_S => {
                    let a = pop_i64(stack);
                    push_f64!(stack, a as f64);
                }
                OP_F64_CONVERT_I64_U => {
                    let a = pop_i64(stack);
                    push_f64!(stack, (a as u64) as f64);
                }
                OP_F64_PROMOTE_F32 => {
                    let a = pop_f32(stack);
                    push_f64!(stack, a as f64);
                }

                // ---- Table / Memory bulk ops ----

                OP_TABLE_INIT => {
                    let n = pop_i32(stack) as u32;
                    let s = pop_i32(stack) as u32;
                    let d = pop_i32(stack) as u32;
                    execute_table_init(
                        store,
                        op.imm_hi() as usize,
                        op.imm_lo() as usize,
                        d, s, n,
                    )?;
                }
                OP_ELEM_DROP => {
                    let elem_idx = op.imm as usize;
                    if elem_idx < store.elem_segments.len() {
                        store.elem_segments[elem_idx] = None;
                    }
                }
                OP_REF_FUNC => {
                    let func_idx = op.imm_u32();
                    stack.push_u64(func_idx as u64);
                }
                OP_REF_NULL => {
                    stack.push_u64(u64::MAX);
                }
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
                    store
                        .memory
                        .copy_within(s as usize..(s + n) as usize, d as usize);
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
                    let shared_table = store
                        .tables
                        .get(table_idx)
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
                    let shared_table = store
                        .tables
                        .get(table_idx)
                        .ok_or_else(|| ExecError::Trap("undefined table".into()))?;
                    let mut table = shared_table.borrow_mut();
                    if idx as usize >= table.len() {
                        return Err(ExecError::oob_table());
                    }
                    table[idx as usize] = if val == u64::MAX {
                        None
                    } else {
                        Some(val as u32)
                    };
                }
                OP_TABLE_SIZE => {
                    let table_idx = op.imm as usize;
                    let shared_table = store
                        .tables
                        .get(table_idx)
                        .ok_or_else(|| ExecError::Trap("undefined table".into()))?;
                    push_i32!(stack, shared_table.borrow().len() as i32);
                }
                OP_TABLE_GROW => {
                    let n = pop_i32(stack) as u32;
                    let init_val = pop_raw(stack);
                    let table_idx = op.imm as usize;
                    let max = store.table_defs.get(table_idx).and_then(|(_, max)| *max);
                    let shared_table = store
                        .tables
                        .get(table_idx)
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
                    let fill = if init_val == u64::MAX {
                        None
                    } else {
                        Some(init_val as u32)
                    };
                    table.resize(new_size as usize, fill);
                    push_i32!(stack, old_size as i32);
                }
                OP_TABLE_COPY => {
                    let n = pop_i32(stack) as u32;
                    let s = pop_i32(stack) as u32;
                    let d = pop_i32(stack) as u32;
                    execute_table_copy(
                        store,
                        op.imm_hi() as usize,
                        op.imm_lo() as usize,
                        d, s, n,
                    )?;
                }
                OP_TABLE_FILL => {
                    let n = pop_i32(stack) as u32;
                    let val = pop_raw(stack);
                    let i = pop_i32(stack) as u32;
                    let table_idx = op.imm as usize;
                    let shared_table = store
                        .tables
                        .get(table_idx)
                        .ok_or_else(|| ExecError::Trap("undefined table".into()))?;
                    let mut table = shared_table.borrow_mut();
                    if i as u64 + n as u64 > table.len() as u64 {
                        return Err(ExecError::oob_table());
                    }
                    let fill = if val == u64::MAX {
                        None
                    } else {
                        Some(val as u32)
                    };
                    for j in 0..n as usize {
                        table[i as usize + j] = fill;
                    }
                }

                _ => {
                    return Err(ExecError::Trap(format!(
                        "unimplemented opcode: {}",
                        op.code
                    )));
                }
            }
        }
    }
}
