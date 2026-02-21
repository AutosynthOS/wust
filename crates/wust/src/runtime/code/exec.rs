//! Flat interpreter loop — no recursion, no native stack overflow.
//!
//! All WASM state lives on the mmap'd Stack. Function calls push InlineFrames
//! instead of creating Rust stack frames. Block control flow uses compile-time
//! entry_depth constants (from BlockDef) — no runtime block frame tracking.

use super::helpers;
use super::stack::Stack;
use crate::runtime::code::module::{FuncDef, Module};
use crate::runtime::error::ExecError;
use crate::runtime::opcode::*;
use crate::runtime::store::Store;
use crate::runtime::value::Value;

/// InlineFrame layout on the WASM stack (3 u32s packed into 2 u64 slots).
///
/// Slot 0: return_sp (low 32) | resume_pc (high 32)
/// Slot 1: func_idx (low 32) | locals_sp (high 32)
const INLINE_FRAME_BYTES: u32 = 16;

#[inline(always)]
fn push_frame(stack: &mut Stack, return_sp: u32, resume_pc: u32, func_idx: u32, locals_sp: u32) {
    stack.push_u64((resume_pc as u64) << 32 | return_sp as u64);
    stack.push_u64((locals_sp as u64) << 32 | func_idx as u64);
}

#[inline(always)]
fn pop_frame(stack: &mut Stack) -> (u32, u32, u32, u32) {
    let slot1 = stack.pop_u64();
    let slot0 = stack.pop_u64();
    let return_sp = slot0 as u32;
    let resume_pc = (slot0 >> 32) as u32;
    let func_idx = slot1 as u32;
    let locals_sp = (slot1 >> 32) as u32;
    (return_sp, resume_pc, func_idx, locals_sp)
}

#[inline(always)]
fn pop_i32(stack: &mut Stack) -> i32 {
    stack.pop_u64() as i32
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

/// Set up the stack frame for a function call and return the new interpreter state.
///
/// Stack layout after setup:
/// ```text
/// [result slots (zeroed)]  ← return_sp points here
/// [InlineFrame]            ← 16 bytes
/// [locals (params + zeros)] ← locals_sp points here
/// ← operand_base = locals_sp + local_count * 8
/// ```
fn setup_call(
    stack: &mut Stack,
    func: &FuncDef,
    args: &[u64],
    prev_return_sp: u32,
    prev_resume_pc: u32,
    prev_func_idx: u32,
    prev_locals_sp: u32,
) -> (u32, u32) {
    // Pre-allocate result slots (zeroed)
    let return_sp = stack.sp();
    for _ in 0..func.result_count {
        stack.push_u64(0);
    }

    // Push InlineFrame
    push_frame(
        stack,
        prev_return_sp,
        prev_resume_pc,
        prev_func_idx,
        prev_locals_sp,
    );

    // Write locals: params first, then zeroed extras
    let locals_sp = stack.sp();
    for i in 0..func.local_count {
        if (i as usize) < args.len() {
            stack.push_u64(args[i as usize]);
        } else {
            stack.push_u64(0);
        }
    }

    let operand_base = stack.sp();
    (locals_sp, operand_base)
}

/// Execute a WASM function using the flat interpreter loop.
///
/// This is the main entry point called from program.rs. It sets up the initial
/// call frame and runs the interpreter until the function returns.
pub(crate) fn execute(
    stack: &mut Stack,
    module: &Module,
    store: &mut Store,
    func_idx: u32,
    args: &[Value],
) -> Result<Vec<Value>, ExecError> {
    let func = module
        .get_func(func_idx)
        .ok_or_else(|| ExecError::Trap(format!("function {func_idx} not found")))?;

    // Convert args to raw u64 bits
    let raw_args: Vec<u64> = args.iter().map(|v| v.to_bits()).collect();

    // Sentinel values for the initial frame — resume_pc = u32::MAX means
    // "return to Rust" when we pop this frame.
    let (mut locals_sp, mut operand_base) = setup_call(stack, func, &raw_args, 0, u32::MAX, 0, 0);
    let mut return_sp = 0u32; // result slots start at SP=0 for initial call
    let mut pc: u32 = 0;
    let mut current_func_idx = func_idx;
    let mut body = &func.body;
    let mut blocks = &func.blocks;
    let mut br_tables = &func.br_tables;
    let mut result_count = func.result_count;

    // Macro for function return: copy results to return_sp, restore caller.
    // Used by OP_RETURN, OP_END at block 0, and br/br_if/br_table targeting block 0.
    macro_rules! do_return {
        () => {{
            let arity = result_count;
            let src_sp = stack.sp() - arity * 8;
            for i in 0..arity {
                let val = stack.read_u64(src_sp + i * 8);
                stack.write_u64(return_sp + i * 8, val);
            }
            stack.set_sp(return_sp + arity * 8);

            // Read InlineFrame (sits right after result slots)
            let frame_sp = return_sp + arity * 8;
            let slot0 = stack.read_u64(frame_sp);
            let slot1 = stack.read_u64(frame_sp + 8);
            let prev_return_sp = slot0 as u32;
            let prev_resume_pc = (slot0 >> 32) as u32;
            let prev_func_idx = slot1 as u32;
            let prev_locals_sp = (slot1 >> 32) as u32;

            if prev_resume_pc == u32::MAX {
                break; // Return to Rust
            }

            pc = prev_resume_pc;
            current_func_idx = prev_func_idx;
            let caller_func = module
                .get_func(current_func_idx)
                .ok_or_else(|| ExecError::Trap(format!("function {current_func_idx} not found")))?;
            body = &caller_func.body;
            blocks = &caller_func.blocks;
            br_tables = &caller_func.br_tables;
            result_count = caller_func.result_count;
            locals_sp = prev_locals_sp;
            operand_base = locals_sp + caller_func.local_count * 8;
            return_sp = prev_return_sp;
        }};
    }

    // Macro for branch: handles both block-level br and function-level return.
    macro_rules! do_br {
        ($block_idx:expr) => {{
            let bi = $block_idx;
            if bi == 0 {
                do_return!();
            } else {
                let block = &blocks[bi as usize];
                let arity = if block.kind == BlockKind::Loop {
                    block.param_arity
                } else {
                    block.result_arity
                };
                let target_sp = operand_base + block.entry_depth * 8;
                let src_sp = stack.sp() - arity * 8;
                for i in 0..arity {
                    let val = stack.read_u64(src_sp + i * 8);
                    stack.write_u64(target_sp + i * 8, val);
                }
                stack.set_sp(target_sp + arity * 8);
                pc = block.br_target;
            }
        }};
    }

    loop {
        if pc as usize >= body.len() {
            // Past the end — treat as implicit return
            break;
        }

        let op = body[pc as usize];
        pc += 1;

        match op.code {
            OP_NOP => {}

            OP_UNREACHABLE => {
                return Err(ExecError::Trap("unreachable".into()));
            }

            // === Block control flow (no-ops or jumps) ===
            OP_BLOCK | OP_LOOP => {
                // No-op at runtime. Metadata is in BlockDef.
            }

            OP_IF => {
                let block_idx = op.imm_u32();
                let cond = pop_i32(stack);
                if cond == 0 {
                    let block = &blocks[block_idx as usize];
                    // Jump to else or past end
                    if block.else_pc != 0 {
                        pc = block.else_pc + 1;
                    } else {
                        pc = block.end_pc + 1;
                    }
                }
            }

            OP_IF_ELSE => {
                let block_idx = op.imm_u32();
                let cond = pop_i32(stack);
                if cond == 0 {
                    let block = &blocks[block_idx as usize];
                    pc = block.else_pc + 1;
                }
            }

            OP_ELSE => {
                // Fell through from then-body — jump past END.
                // Find which block we're in by scanning backwards for the IF.
                // But we can find it because OP_ELSE is always preceded by a known block.
                // Actually, we need to find the enclosing if block. The OP_ELSE
                // instruction's position tells us which block it belongs to.
                // We need to find the block whose else_pc == pc-1.
                for block in blocks.iter() {
                    if block.else_pc == pc - 1 {
                        pc = block.end_pc + 1;
                        break;
                    }
                }
            }

            OP_END => {
                if blocks[0].end_pc == pc - 1 {
                    do_return!();
                }
                // else: block-level END — no-op
            }

            OP_BR => {
                let block_idx = op.imm_u32();
                do_br!(block_idx);
            }

            OP_BR_IF => {
                let block_idx = op.imm_u32();
                let cond = pop_i32(stack);
                if cond != 0 {
                    do_br!(block_idx);
                }
            }

            OP_BR_TABLE => {
                let table_idx = op.imm_u32();
                let br_table = &br_tables[table_idx as usize];
                let idx = pop_i32(stack) as u32;
                let block_idx = if (idx as usize) < br_table.targets.len() {
                    br_table.targets[idx as usize]
                } else {
                    br_table.default
                };
                do_br!(block_idx);
            }

            OP_RETURN => {
                do_return!();
            }

            // === Function calls ===
            OP_CALL => {
                let callee_idx = op.imm_u32();

                // Handle imported (host) functions
                if module.is_import(callee_idx) {
                    let callee_type_idx = module.func_types[callee_idx as usize];
                    let callee_type = &module.types[callee_type_idx as usize];
                    let param_count = callee_type.params().len();
                    let result_count = callee_type.results().len();

                    // Pop args from stack
                    let mut host_args = Vec::with_capacity(param_count);
                    let args_sp = stack.sp() - param_count as u32 * 8;
                    for i in 0..param_count {
                        let bits = stack.read_u64(args_sp + i as u32 * 8);
                        host_args.push(Value::from_bits(bits, callee_type.params()[i]));
                    }
                    stack.set_sp(args_sp);

                    let host_fn = store.host_funcs.get(callee_idx as usize).ok_or_else(|| {
                        ExecError::Trap(format!("unresolved import function {callee_idx}"))
                    })?;
                    let results = host_fn(&host_args, &mut store.memory)
                        .map_err(|e| ExecError::Trap(format!("trap: {e}")))?;

                    for val in &results {
                        stack.push_u64(val.to_bits());
                    }
                    continue;
                }

                let callee = module
                    .get_func(callee_idx)
                    .ok_or_else(|| ExecError::Trap(format!("function {callee_idx} not found")))?;

                // Pop params from caller's operand stack into temp
                let param_count = callee.param_count;
                let mut params = Vec::with_capacity(param_count as usize);
                let params_sp = stack.sp() - param_count * 8;
                for i in 0..param_count {
                    params.push(stack.read_u64(params_sp + i * 8));
                }
                stack.set_sp(params_sp);

                // Set up callee frame
                let (new_locals_sp, new_operand_base) = setup_call(
                    stack,
                    callee,
                    &params,
                    return_sp,
                    pc, // resume at instruction after CALL
                    current_func_idx,
                    locals_sp,
                );

                // Switch to callee
                return_sp = params_sp;
                pc = 0;
                current_func_idx = callee_idx;
                body = &callee.body;
                blocks = &callee.blocks;
                br_tables = &callee.br_tables;
                result_count = callee.result_count;
                locals_sp = new_locals_sp;
                operand_base = new_operand_base;
            }

            OP_CALL_INDIRECT => {
                let type_idx = op.imm_hi();
                let table_idx = op.imm_lo();

                // Pop table element index
                let elem_idx = pop_i32(stack) as u32;

                // Resolve function index from table
                let callee_idx = helpers::resolve_table_element(store, table_idx, elem_idx)?;

                // Type check
                let expected_type = &module.types[type_idx as usize];
                helpers::check_indirect_type(module, callee_idx, expected_type)?;

                // Handle imported (host) functions
                if module.is_import(callee_idx) {
                    let callee_type = expected_type;
                    let param_count = callee_type.params().len();

                    let mut host_args = Vec::with_capacity(param_count);
                    let args_sp = stack.sp() - param_count as u32 * 8;
                    for i in 0..param_count {
                        let bits = stack.read_u64(args_sp + i as u32 * 8);
                        host_args.push(Value::from_bits(bits, callee_type.params()[i]));
                    }
                    stack.set_sp(args_sp);

                    let host_fn = store.host_funcs.get(callee_idx as usize).ok_or_else(|| {
                        ExecError::Trap(format!("unresolved import function {callee_idx}"))
                    })?;
                    let results = host_fn(&host_args, &mut store.memory)
                        .map_err(|e| ExecError::Trap(format!("trap: {e}")))?;

                    for val in &results {
                        stack.push_u64(val.to_bits());
                    }
                    continue;
                }

                let callee = module
                    .get_func(callee_idx)
                    .ok_or_else(|| ExecError::Trap(format!("function {callee_idx} not found")))?;

                let param_count = callee.param_count;
                let mut params = Vec::with_capacity(param_count as usize);
                let params_sp = stack.sp() - param_count * 8;
                for i in 0..param_count {
                    params.push(stack.read_u64(params_sp + i * 8));
                }
                stack.set_sp(params_sp);

                let (new_locals_sp, new_operand_base) = setup_call(
                    stack,
                    callee,
                    &params,
                    return_sp,
                    pc,
                    current_func_idx,
                    locals_sp,
                );

                return_sp = params_sp;
                pc = 0;
                current_func_idx = callee_idx;
                body = &callee.body;
                blocks = &callee.blocks;
                br_tables = &callee.br_tables;
                result_count = callee.result_count;
                locals_sp = new_locals_sp;
                operand_base = new_operand_base;
            }

            // === Locals / Globals ===
            OP_LOCAL_GET => {
                let idx = op.imm_u32();
                let val = stack.read_u64(locals_sp + idx * 8);
                stack.push_u64(val);
            }

            OP_LOCAL_SET => {
                let idx = op.imm_u32();
                let val = stack.pop_u64();
                stack.write_u64(locals_sp + idx * 8, val);
            }

            OP_LOCAL_TEE => {
                let idx = op.imm_u32();
                let val = stack.read_u64(stack.sp() - 8); // peek
                stack.write_u64(locals_sp + idx * 8, val);
            }

            OP_GLOBAL_GET => {
                let idx = op.imm_u32();
                let val = store.globals[idx as usize].to_bits();
                stack.push_u64(val);
            }

            OP_GLOBAL_SET => {
                let idx = op.imm_u32();
                let bits = stack.pop_u64();
                let existing = &store.globals[idx as usize];
                store.globals[idx as usize] = helpers::coerce_bits_to_global(bits, existing)?;
            }

            // === Constants ===
            OP_I32_CONST => {
                stack.push_u64(op.imm_u32() as u64);
            }

            OP_I64_CONST => {
                stack.push_u64(op.imm_u64());
            }

            OP_F32_CONST => {
                stack.push_u64(op.imm_u32() as u64);
            }

            OP_F64_CONST => {
                stack.push_u64(op.imm_u64());
            }

            // === Drop / Select ===
            OP_DROP => {
                stack.pop_u64();
            }

            OP_SELECT => {
                let cond = pop_i32(stack);
                let b = stack.pop_u64();
                let a = stack.pop_u64();
                stack.push_u64(if cond != 0 { a } else { b });
            }

            // === Memory ===
            OP_I32_LOAD => {
                mem_load!(
                    stack,
                    store,
                    op.imm_u64(),
                    4,
                    |b: [u8; 4]| i32::from_le_bytes(b) as u32 as u64
                );
            }
            OP_I64_LOAD => {
                mem_load!(stack, store, op.imm_u64(), 8, |b: [u8; 8]| {
                    u64::from_le_bytes(b)
                });
            }
            OP_F32_LOAD => {
                mem_load!(
                    stack,
                    store,
                    op.imm_u64(),
                    4,
                    |b: [u8; 4]| u32::from_le_bytes(b) as u64
                );
            }
            OP_F64_LOAD => {
                mem_load!(stack, store, op.imm_u64(), 8, |b: [u8; 8]| {
                    u64::from_le_bytes(b)
                });
            }
            OP_I32_LOAD8_S => {
                mem_load!(
                    stack,
                    store,
                    op.imm_u64(),
                    1,
                    |b: [u8; 1]| i8::from_le_bytes(b) as i32 as u32 as u64
                );
            }
            OP_I32_LOAD8_U => {
                mem_load!(
                    stack,
                    store,
                    op.imm_u64(),
                    1,
                    |b: [u8; 1]| u8::from_le_bytes(b) as u64
                );
            }
            OP_I32_LOAD16_S => {
                mem_load!(
                    stack,
                    store,
                    op.imm_u64(),
                    2,
                    |b: [u8; 2]| i16::from_le_bytes(b) as i32 as u32 as u64
                );
            }
            OP_I32_LOAD16_U => {
                mem_load!(
                    stack,
                    store,
                    op.imm_u64(),
                    2,
                    |b: [u8; 2]| u16::from_le_bytes(b) as u64
                );
            }
            OP_I64_LOAD8_S => {
                mem_load!(
                    stack,
                    store,
                    op.imm_u64(),
                    1,
                    |b: [u8; 1]| i8::from_le_bytes(b) as i64 as u64
                );
            }
            OP_I64_LOAD8_U => {
                mem_load!(
                    stack,
                    store,
                    op.imm_u64(),
                    1,
                    |b: [u8; 1]| u8::from_le_bytes(b) as u64
                );
            }
            OP_I64_LOAD16_S => {
                mem_load!(
                    stack,
                    store,
                    op.imm_u64(),
                    2,
                    |b: [u8; 2]| i16::from_le_bytes(b) as i64 as u64
                );
            }
            OP_I64_LOAD16_U => {
                mem_load!(
                    stack,
                    store,
                    op.imm_u64(),
                    2,
                    |b: [u8; 2]| u16::from_le_bytes(b) as u64
                );
            }
            OP_I64_LOAD32_S => {
                mem_load!(
                    stack,
                    store,
                    op.imm_u64(),
                    4,
                    |b: [u8; 4]| i32::from_le_bytes(b) as i64 as u64
                );
            }
            OP_I64_LOAD32_U => {
                mem_load!(
                    stack,
                    store,
                    op.imm_u64(),
                    4,
                    |b: [u8; 4]| u32::from_le_bytes(b) as u64
                );
            }

            OP_I32_STORE => {
                mem_store!(stack, store, op.imm_u64(), pop_i32, |v: i32| (v as u32)
                    .to_le_bytes());
            }
            OP_I64_STORE => {
                mem_store!(stack, store, op.imm_u64(), pop_i64, |v: i64| v
                    .to_le_bytes());
            }
            OP_F32_STORE => {
                mem_store!(stack, store, op.imm_u64(), pop_f32, |v: f32| v
                    .to_bits()
                    .to_le_bytes());
            }
            OP_F64_STORE => {
                mem_store!(stack, store, op.imm_u64(), pop_f64, |v: f64| v
                    .to_bits()
                    .to_le_bytes());
            }
            OP_I32_STORE8 => {
                mem_store!(stack, store, op.imm_u64(), pop_i32, |v: i32| (v as u8)
                    .to_le_bytes());
            }
            OP_I32_STORE16 => {
                mem_store!(stack, store, op.imm_u64(), pop_i32, |v: i32| (v as u16)
                    .to_le_bytes());
            }
            OP_I64_STORE8 => {
                mem_store!(stack, store, op.imm_u64(), pop_i64, |v: i64| (v as u8)
                    .to_le_bytes());
            }
            OP_I64_STORE16 => {
                mem_store!(stack, store, op.imm_u64(), pop_i64, |v: i64| (v as u16)
                    .to_le_bytes());
            }
            OP_I64_STORE32 => {
                mem_store!(stack, store, op.imm_u64(), pop_i64, |v: i64| (v as u32)
                    .to_le_bytes());
            }

            OP_MEMORY_SIZE => {
                let pages = (store.memory.len() / 65536) as i32;
                push_i32!(stack, pages);
            }

            OP_MEMORY_GROW => {
                let delta = pop_i32(stack) as u32;
                let old_pages = (store.memory.len() / 65536) as u32;
                let new_pages = old_pages + delta;
                // Check 65536-page limit (4GB)
                if new_pages > 65536 {
                    push_i32!(stack, -1i32);
                } else {
                    store.memory.resize(new_pages as usize * 65536, 0);
                    push_i32!(stack, old_pages as i32);
                }
            }

            // === i32 comparison ===
            OP_I32_EQZ => {
                let a = pop_i32(stack);
                push_i32!(stack, if a == 0 { 1i32 } else { 0i32 });
            }
            OP_I32_EQ => {
                cmpop_i32!(stack, |a: i32, b: i32| a == b);
            }
            OP_I32_NE => {
                cmpop_i32!(stack, |a: i32, b: i32| a != b);
            }
            OP_I32_LT_S => {
                cmpop_i32!(stack, |a: i32, b: i32| a < b);
            }
            OP_I32_LT_U => {
                cmpop_i32!(stack, |a: i32, b: i32| (a as u32) < (b as u32));
            }
            OP_I32_GT_S => {
                cmpop_i32!(stack, |a: i32, b: i32| a > b);
            }
            OP_I32_GT_U => {
                cmpop_i32!(stack, |a: i32, b: i32| (a as u32) > (b as u32));
            }
            OP_I32_LE_S => {
                cmpop_i32!(stack, |a: i32, b: i32| a <= b);
            }
            OP_I32_LE_U => {
                cmpop_i32!(stack, |a: i32, b: i32| (a as u32) <= (b as u32));
            }
            OP_I32_GE_S => {
                cmpop_i32!(stack, |a: i32, b: i32| a >= b);
            }
            OP_I32_GE_U => {
                cmpop_i32!(stack, |a: i32, b: i32| (a as u32) >= (b as u32));
            }

            // === i32 arithmetic ===
            OP_I32_CLZ => {
                unop_i32!(stack, |a: i32| a.leading_zeros() as i32);
            }
            OP_I32_CTZ => {
                unop_i32!(stack, |a: i32| a.trailing_zeros() as i32);
            }
            OP_I32_POPCNT => {
                unop_i32!(stack, |a: i32| a.count_ones() as i32);
            }
            OP_I32_ADD => {
                binop_i32!(stack, |a: i32, b: i32| a.wrapping_add(b));
            }
            OP_I32_SUB => {
                binop_i32!(stack, |a: i32, b: i32| a.wrapping_sub(b));
            }
            OP_I32_MUL => {
                binop_i32!(stack, |a: i32, b: i32| a.wrapping_mul(b));
            }
            OP_I32_DIV_S => {
                div_s!(stack, pop_i32, i32);
            }
            OP_I32_DIV_U => {
                div_u_i32!(stack);
            }
            OP_I32_REM_S => {
                rem_s_i32!(stack);
            }
            OP_I32_REM_U => {
                rem_u_i32!(stack);
            }
            OP_I32_AND => {
                binop_i32!(stack, |a: i32, b: i32| a & b);
            }
            OP_I32_OR => {
                binop_i32!(stack, |a: i32, b: i32| a | b);
            }
            OP_I32_XOR => {
                binop_i32!(stack, |a: i32, b: i32| a ^ b);
            }
            OP_I32_SHL => {
                binop_i32!(stack, |a: i32, b: i32| a.wrapping_shl(b as u32 & 31));
            }
            OP_I32_SHR_S => {
                binop_i32!(stack, |a: i32, b: i32| a.wrapping_shr(b as u32 & 31));
            }
            OP_I32_SHR_U => {
                binop_i32!(
                    stack,
                    |a: i32, b: i32| ((a as u32).wrapping_shr(b as u32 & 31)) as i32
                );
            }
            OP_I32_ROTL => {
                binop_i32!(
                    stack,
                    |a: i32, b: i32| (a as u32).rotate_left(b as u32 & 31) as i32
                );
            }
            OP_I32_ROTR => {
                binop_i32!(
                    stack,
                    |a: i32, b: i32| (a as u32).rotate_right(b as u32 & 31) as i32
                );
            }

            // === i64 comparison ===
            OP_I64_EQZ => {
                let a = pop_i64(stack);
                push_i32!(stack, if a == 0 { 1i32 } else { 0i32 });
            }
            OP_I64_EQ => {
                cmpop_i64!(stack, |a: i64, b: i64| a == b);
            }
            OP_I64_NE => {
                cmpop_i64!(stack, |a: i64, b: i64| a != b);
            }
            OP_I64_LT_S => {
                cmpop_i64!(stack, |a: i64, b: i64| a < b);
            }
            OP_I64_LT_U => {
                cmpop_i64!(stack, |a: i64, b: i64| (a as u64) < (b as u64));
            }
            OP_I64_GT_S => {
                cmpop_i64!(stack, |a: i64, b: i64| a > b);
            }
            OP_I64_GT_U => {
                cmpop_i64!(stack, |a: i64, b: i64| (a as u64) > (b as u64));
            }
            OP_I64_LE_S => {
                cmpop_i64!(stack, |a: i64, b: i64| a <= b);
            }
            OP_I64_LE_U => {
                cmpop_i64!(stack, |a: i64, b: i64| (a as u64) <= (b as u64));
            }
            OP_I64_GE_S => {
                cmpop_i64!(stack, |a: i64, b: i64| a >= b);
            }
            OP_I64_GE_U => {
                cmpop_i64!(stack, |a: i64, b: i64| (a as u64) >= (b as u64));
            }

            // === i64 arithmetic ===
            OP_I64_CLZ => {
                unop_i64!(stack, |a: i64| a.leading_zeros() as i64);
            }
            OP_I64_CTZ => {
                unop_i64!(stack, |a: i64| a.trailing_zeros() as i64);
            }
            OP_I64_POPCNT => {
                unop_i64!(stack, |a: i64| a.count_ones() as i64);
            }
            OP_I64_ADD => {
                binop_i64!(stack, |a: i64, b: i64| a.wrapping_add(b));
            }
            OP_I64_SUB => {
                binop_i64!(stack, |a: i64, b: i64| a.wrapping_sub(b));
            }
            OP_I64_MUL => {
                binop_i64!(stack, |a: i64, b: i64| a.wrapping_mul(b));
            }
            OP_I64_DIV_S => {
                div_s_i64!(stack);
            }
            OP_I64_DIV_U => {
                div_u_i64!(stack);
            }
            OP_I64_REM_S => {
                rem_s_i64!(stack);
            }
            OP_I64_REM_U => {
                rem_u_i64!(stack);
            }
            OP_I64_AND => {
                binop_i64!(stack, |a: i64, b: i64| a & b);
            }
            OP_I64_OR => {
                binop_i64!(stack, |a: i64, b: i64| a | b);
            }
            OP_I64_XOR => {
                binop_i64!(stack, |a: i64, b: i64| a ^ b);
            }
            OP_I64_SHL => {
                binop_i64!(stack, |a: i64, b: i64| a.wrapping_shl((b & 63) as u32));
            }
            OP_I64_SHR_S => {
                binop_i64!(stack, |a: i64, b: i64| a.wrapping_shr((b & 63) as u32));
            }
            OP_I64_SHR_U => {
                binop_i64!(
                    stack,
                    |a: i64, b: i64| ((a as u64).wrapping_shr((b & 63) as u32)) as i64
                );
            }
            OP_I64_ROTL => {
                binop_i64!(
                    stack,
                    |a: i64, b: i64| (a as u64).rotate_left((b & 63) as u32) as i64
                );
            }
            OP_I64_ROTR => {
                binop_i64!(
                    stack,
                    |a: i64, b: i64| (a as u64).rotate_right((b & 63) as u32) as i64
                );
            }

            // === Conversions ===
            OP_I32_WRAP_I64 => {
                let a = pop_i64(stack);
                push_i32!(stack, a as i32);
            }
            OP_I64_EXTEND_I32_S => {
                let a = pop_i32(stack);
                push_i64!(stack, a as i64);
            }
            OP_I64_EXTEND_I32_U => {
                let a = pop_i32(stack) as u32;
                push_i64!(stack, a as u64 as i64);
            }

            // === f32 comparison ===
            OP_F32_EQ => {
                cmpop_f32!(stack, |a: f32, b: f32| a == b);
            }
            OP_F32_NE => {
                cmpop_f32!(stack, |a: f32, b: f32| a != b);
            }
            OP_F32_LT => {
                cmpop_f32!(stack, |a: f32, b: f32| a < b);
            }
            OP_F32_GT => {
                cmpop_f32!(stack, |a: f32, b: f32| a > b);
            }
            OP_F32_LE => {
                cmpop_f32!(stack, |a: f32, b: f32| a <= b);
            }
            OP_F32_GE => {
                cmpop_f32!(stack, |a: f32, b: f32| a >= b);
            }

            // === f64 comparison ===
            OP_F64_EQ => {
                cmpop_f64!(stack, |a: f64, b: f64| a == b);
            }
            OP_F64_NE => {
                cmpop_f64!(stack, |a: f64, b: f64| a != b);
            }
            OP_F64_LT => {
                cmpop_f64!(stack, |a: f64, b: f64| a < b);
            }
            OP_F64_GT => {
                cmpop_f64!(stack, |a: f64, b: f64| a > b);
            }
            OP_F64_LE => {
                cmpop_f64!(stack, |a: f64, b: f64| a <= b);
            }
            OP_F64_GE => {
                cmpop_f64!(stack, |a: f64, b: f64| a >= b);
            }

            // === f32 arithmetic ===
            OP_F32_ABS => {
                unop_f32!(stack, |a: f32| a.abs());
            }
            OP_F32_NEG => {
                unop_f32!(stack, |a: f32| -a);
            }
            OP_F32_CEIL => {
                unop_f32!(stack, |a: f32| a.ceil());
            }
            OP_F32_FLOOR => {
                unop_f32!(stack, |a: f32| a.floor());
            }
            OP_F32_TRUNC => {
                unop_f32!(stack, |a: f32| a.trunc());
            }
            OP_F32_NEAREST => {
                unop_f32!(stack, wasm_nearest_f32);
            }
            OP_F32_SQRT => {
                unop_f32!(stack, |a: f32| a.sqrt());
            }
            OP_F32_ADD => {
                binop_f32!(stack, |a: f32, b: f32| a + b);
            }
            OP_F32_SUB => {
                binop_f32!(stack, |a: f32, b: f32| a - b);
            }
            OP_F32_MUL => {
                binop_f32!(stack, |a: f32, b: f32| a * b);
            }
            OP_F32_DIV => {
                binop_f32!(stack, |a: f32, b: f32| a / b);
            }
            OP_F32_MIN => {
                binop_f32!(stack, wasm_min_f32);
            }
            OP_F32_MAX => {
                binop_f32!(stack, wasm_max_f32);
            }
            OP_F32_COPYSIGN => {
                binop_f32!(stack, |a: f32, b: f32| f32::copysign(a, b));
            }

            // === f64 arithmetic ===
            OP_F64_ABS => {
                unop_f64!(stack, |a: f64| a.abs());
            }
            OP_F64_NEG => {
                unop_f64!(stack, |a: f64| -a);
            }
            OP_F64_CEIL => {
                unop_f64!(stack, |a: f64| a.ceil());
            }
            OP_F64_FLOOR => {
                unop_f64!(stack, |a: f64| a.floor());
            }
            OP_F64_TRUNC => {
                unop_f64!(stack, |a: f64| a.trunc());
            }
            OP_F64_NEAREST => {
                unop_f64!(stack, wasm_nearest_f64);
            }
            OP_F64_SQRT => {
                unop_f64!(stack, |a: f64| a.sqrt());
            }
            OP_F64_ADD => {
                binop_f64!(stack, |a: f64, b: f64| a + b);
            }
            OP_F64_SUB => {
                binop_f64!(stack, |a: f64, b: f64| a - b);
            }
            OP_F64_MUL => {
                binop_f64!(stack, |a: f64, b: f64| a * b);
            }
            OP_F64_DIV => {
                binop_f64!(stack, |a: f64, b: f64| a / b);
            }
            OP_F64_MIN => {
                binop_f64!(stack, wasm_min_f64);
            }
            OP_F64_MAX => {
                binop_f64!(stack, wasm_max_f64);
            }
            OP_F64_COPYSIGN => {
                binop_f64!(stack, |a: f64, b: f64| f64::copysign(a, b));
            }

            // === Float-int conversions ===
            OP_I32_TRUNC_F32_S => {
                trunc_op!(
                    stack,
                    pop_f32,
                    push_i32,
                    i32,
                    2147483648.0_f32,
                    -2147483904.0_f32
                );
            }
            OP_I32_TRUNC_F32_U => {
                trunc_op_u!(stack, pop_f32, push_i32, u32, i32, 4294967296.0_f32);
            }
            OP_I32_TRUNC_F64_S => {
                trunc_op!(
                    stack,
                    pop_f64,
                    push_i32,
                    i32,
                    2147483648.0_f64,
                    -2147483649.0_f64
                );
            }
            OP_I32_TRUNC_F64_U => {
                trunc_op_u!(stack, pop_f64, push_i32, u32, i32, 4294967296.0_f64);
            }
            OP_I64_TRUNC_F32_S => {
                trunc_op!(
                    stack,
                    pop_f32,
                    push_i64,
                    i64,
                    9223372036854775808.0_f32,
                    -9223373136366403584.0_f32
                );
            }
            OP_I64_TRUNC_F32_U => {
                trunc_op_u!(
                    stack,
                    pop_f32,
                    push_i64,
                    u64,
                    i64,
                    18446744073709551616.0_f32
                );
            }
            OP_I64_TRUNC_F64_S => {
                trunc_op!(
                    stack,
                    pop_f64,
                    push_i64,
                    i64,
                    9223372036854775808.0_f64,
                    -9223372036854777856.0_f64
                );
            }
            OP_I64_TRUNC_F64_U => {
                trunc_op_u!(
                    stack,
                    pop_f64,
                    push_i64,
                    u64,
                    i64,
                    18446744073709551616.0_f64
                );
            }

            OP_F32_CONVERT_I32_S => {
                let a = pop_i32(stack);
                push_f32!(stack, a as f32);
            }
            OP_F32_CONVERT_I32_U => {
                let a = pop_i32(stack) as u32;
                push_f32!(stack, a as f32);
            }
            OP_F32_CONVERT_I64_S => {
                let a = pop_i64(stack);
                push_f32!(stack, a as f32);
            }
            OP_F32_CONVERT_I64_U => {
                let a = pop_i64(stack) as u64;
                push_f32!(stack, a as f32);
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
                let a = pop_i32(stack) as u32;
                push_f64!(stack, a as f64);
            }
            OP_F64_CONVERT_I64_S => {
                let a = pop_i64(stack);
                push_f64!(stack, a as f64);
            }
            OP_F64_CONVERT_I64_U => {
                let a = pop_i64(stack) as u64;
                push_f64!(stack, a as f64);
            }
            OP_F64_PROMOTE_F32 => {
                let a = pop_f32(stack);
                push_f64!(stack, a as f64);
            }

            // === Reinterpret ===
            OP_I32_REINTERPRET_F32 => { /* bits don't change, u64 on stack already holds f32 bits */
            }
            OP_I64_REINTERPRET_F64 => { /* bits don't change */ }
            OP_F32_REINTERPRET_I32 => { /* bits don't change */ }
            OP_F64_REINTERPRET_I64 => { /* bits don't change */ }

            // === Sign extension ===
            OP_I32_EXTEND8_S => {
                let a = pop_i32(stack);
                push_i32!(stack, (a as i8) as i32);
            }
            OP_I32_EXTEND16_S => {
                let a = pop_i32(stack);
                push_i32!(stack, (a as i16) as i32);
            }
            OP_I64_EXTEND8_S => {
                let a = pop_i64(stack);
                push_i64!(stack, (a as i8) as i64);
            }
            OP_I64_EXTEND16_S => {
                let a = pop_i64(stack);
                push_i64!(stack, (a as i16) as i64);
            }
            OP_I64_EXTEND32_S => {
                let a = pop_i64(stack);
                push_i64!(stack, (a as i32) as i64);
            }

            // === Saturating truncation ===
            OP_I32_TRUNC_SAT_F32_S => {
                trunc_sat_s!(
                    stack,
                    pop_f32,
                    push_i32,
                    i32,
                    2147483648.0_f32,
                    -2147483904.0_f32
                );
            }
            OP_I32_TRUNC_SAT_F32_U => {
                trunc_sat_u!(stack, pop_f32, push_i32, u32, i32, 4294967296.0_f32);
            }
            OP_I32_TRUNC_SAT_F64_S => {
                trunc_sat_s!(
                    stack,
                    pop_f64,
                    push_i32,
                    i32,
                    2147483648.0_f64,
                    -2147483649.0_f64
                );
            }
            OP_I32_TRUNC_SAT_F64_U => {
                trunc_sat_u!(stack, pop_f64, push_i32, u32, i32, 4294967296.0_f64);
            }
            OP_I64_TRUNC_SAT_F32_S => {
                trunc_sat_s!(
                    stack,
                    pop_f32,
                    push_i64,
                    i64,
                    9223372036854775808.0_f32,
                    -9223373136366403584.0_f32
                );
            }
            OP_I64_TRUNC_SAT_F32_U => {
                trunc_sat_u!(
                    stack,
                    pop_f32,
                    push_i64,
                    u64,
                    i64,
                    18446744073709551616.0_f32
                );
            }
            OP_I64_TRUNC_SAT_F64_S => {
                trunc_sat_s!(
                    stack,
                    pop_f64,
                    push_i64,
                    i64,
                    9223372036854775808.0_f64,
                    -9223372036854777856.0_f64
                );
            }
            OP_I64_TRUNC_SAT_F64_U => {
                trunc_sat_u!(
                    stack,
                    pop_f64,
                    push_i64,
                    u64,
                    i64,
                    18446744073709551616.0_f64
                );
            }

            // === Reference types ===
            OP_REF_FUNC => {
                stack.push_u64(op.imm_u32() as u64);
            }
            OP_REF_NULL => {
                stack.push_u64(u64::MAX); // sentinel for null ref
            }
            OP_REF_IS_NULL => {
                let val = stack.pop_u64();
                push_i32!(stack, if val == u64::MAX { 1i32 } else { 0i32 });
            }

            // === Table operations ===
            OP_TABLE_GET => {
                let table_idx = op.imm_u32();
                let idx = pop_i32(stack) as u32;
                let shared = &store.tables[table_idx as usize];
                let table = shared.borrow();
                if idx as usize >= table.len() {
                    return Err(ExecError::oob_table());
                }
                match table[idx as usize] {
                    Some(func_idx) => stack.push_u64(func_idx as u64),
                    None => stack.push_u64(u64::MAX),
                }
            }
            OP_TABLE_SET => {
                let table_idx = op.imm_u32();
                let val = stack.pop_u64();
                let idx = pop_i32(stack) as u32;
                let shared = &store.tables[table_idx as usize];
                let mut table = shared.borrow_mut();
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
                let table_idx = op.imm_u32();
                let shared = &store.tables[table_idx as usize];
                let table = shared.borrow();
                push_i32!(stack, table.len() as i32);
            }
            OP_TABLE_GROW => {
                let table_idx = op.imm_u32();
                let n = pop_i32(stack) as u32;
                let val = stack.pop_u64();
                let shared = &store.tables[table_idx as usize];
                let mut table = shared.borrow_mut();
                let old_len = table.len() as u32;
                let entry = if val == u64::MAX {
                    None
                } else {
                    Some(val as u32)
                };
                // Check if growth exceeds max (if set) or u32 max
                let new_len = old_len as u64 + n as u64;
                if new_len > u32::MAX as u64 {
                    push_i32!(stack, -1i32);
                } else {
                    table.resize(new_len as usize, entry);
                    push_i32!(stack, old_len as i32);
                }
            }
            OP_TABLE_INIT => {
                let elem_idx = op.imm_hi();
                let table_idx = op.imm_lo();
                let count = pop_i32(stack) as u32;
                let src = pop_i32(stack) as u32;
                let dst = pop_i32(stack) as u32;
                helpers::execute_table_init(
                    store,
                    elem_idx as usize,
                    table_idx as usize,
                    dst,
                    src,
                    count,
                )?;
            }
            OP_ELEM_DROP => {
                let idx = op.imm_u32() as usize;
                if idx < store.elem_segments.len() {
                    store.elem_segments[idx] = None;
                }
            }
            OP_TABLE_COPY => {
                let dst_table = op.imm_hi();
                let src_table = op.imm_lo();
                let count = pop_i32(stack) as u32;
                let src = pop_i32(stack) as u32;
                let dst = pop_i32(stack) as u32;
                helpers::execute_table_copy(
                    store,
                    dst_table as usize,
                    src_table as usize,
                    dst,
                    src,
                    count,
                )?;
            }
            OP_TABLE_FILL => {
                let table_idx = op.imm_u32();
                let count = pop_i32(stack) as u32;
                let val = stack.pop_u64();
                let idx = pop_i32(stack) as u32;
                let shared = &store.tables[table_idx as usize];
                let mut table = shared.borrow_mut();
                if idx as u64 + count as u64 > table.len() as u64 {
                    return Err(ExecError::oob_table());
                }
                let entry = if val == u64::MAX {
                    None
                } else {
                    Some(val as u32)
                };
                for i in 0..count {
                    table[(idx + i) as usize] = entry;
                }
            }

            // === Bulk memory ===
            OP_MEMORY_INIT => {
                let seg_idx = op.imm_u32();
                let count = pop_i32(stack) as u32;
                let src = pop_i32(stack) as u32;
                let dst = pop_i32(stack) as u32;
                helpers::execute_memory_init(store, seg_idx as usize, dst, src, count)?;
            }
            OP_DATA_DROP => {
                let idx = op.imm_u32() as usize;
                if idx < store.data_segments.len() {
                    store.data_segments[idx] = None;
                }
            }
            OP_MEMORY_COPY => {
                let count = pop_i32(stack) as u32;
                let src = pop_i32(stack) as u32;
                let dst = pop_i32(stack) as u32;
                let len = store.memory.len() as u64;
                if src as u64 + count as u64 > len || dst as u64 + count as u64 > len {
                    return Err(ExecError::oob_memory());
                }
                store
                    .memory
                    .copy_within(src as usize..(src + count) as usize, dst as usize);
            }
            OP_MEMORY_FILL => {
                let count = pop_i32(stack) as u32;
                let val = pop_i32(stack) as u8;
                let dst = pop_i32(stack) as u32;
                if dst as u64 + count as u64 > store.memory.len() as u64 {
                    return Err(ExecError::oob_memory());
                }
                for i in 0..count {
                    store.memory[(dst + i) as usize] = val;
                }
            }

            // === Superinstructions ===
            OP_LOCAL_GET_I32_CONST => {
                let local_idx = op.imm_hi();
                let val = op.imm_lo();
                let local_val = stack.read_u64(locals_sp + local_idx * 8);
                stack.push_u64(local_val);
                stack.push_u64(val as u64);
            }
            OP_LOCAL_GET_LOCAL_GET => {
                let a = op.imm_hi();
                let b = op.imm_lo();
                stack.push_u64(stack.read_u64(locals_sp + a * 8));
                stack.push_u64(stack.read_u64(locals_sp + b * 8));
            }

            _ => {
                return Err(ExecError::Trap(format!("unsupported opcode {}", op.code)));
            }
        }
    }

    // Read results from position 0 (the return_sp of the initial call)
    let initial_result_count = result_count;
    let func_type = &module.types[module.func_types[func_idx as usize] as usize];
    let mut results = Vec::with_capacity(initial_result_count as usize);
    for i in 0..initial_result_count {
        let bits = stack.read_u64(i * 8);
        results.push(Value::from_bits(bits, func_type.results()[i as usize]));
    }
    Ok(results)
}

// === WASM-specific float helpers ===

#[inline(always)]
fn wasm_nearest_f32(a: f32) -> f32 {
    let rounded = a.round();
    // Tie-breaking: round to even
    if (a - rounded).abs() == 0.5 && rounded % 2.0 != 0.0 {
        rounded - rounded.signum()
    } else {
        rounded
    }
}

#[inline(always)]
fn wasm_nearest_f64(a: f64) -> f64 {
    let rounded = a.round();
    if (a - rounded).abs() == 0.5 && rounded % 2.0 != 0.0 {
        rounded - rounded.signum()
    } else {
        rounded
    }
}

#[inline(always)]
fn wasm_min_f32(a: f32, b: f32) -> f32 {
    if a.is_nan() || b.is_nan() {
        f32::NAN
    } else if a == 0.0 && b == 0.0 {
        if a.is_sign_negative() || b.is_sign_negative() {
            -0.0_f32
        } else {
            0.0_f32
        }
    } else {
        a.min(b)
    }
}

#[inline(always)]
fn wasm_max_f32(a: f32, b: f32) -> f32 {
    if a.is_nan() || b.is_nan() {
        f32::NAN
    } else if a == 0.0 && b == 0.0 {
        if a.is_sign_positive() || b.is_sign_positive() {
            0.0_f32
        } else {
            -0.0_f32
        }
    } else {
        a.max(b)
    }
}

#[inline(always)]
fn wasm_min_f64(a: f64, b: f64) -> f64 {
    if a.is_nan() || b.is_nan() {
        f64::NAN
    } else if a == 0.0 && b == 0.0 {
        if a.is_sign_negative() || b.is_sign_negative() {
            -0.0_f64
        } else {
            0.0_f64
        }
    } else {
        a.min(b)
    }
}

#[inline(always)]
fn wasm_max_f64(a: f64, b: f64) -> f64 {
    if a.is_nan() || b.is_nan() {
        f64::NAN
    } else if a == 0.0 && b == 0.0 {
        if a.is_sign_positive() || b.is_sign_positive() {
            0.0_f64
        } else {
            -0.0_f64
        }
    } else {
        a.max(b)
    }
}
