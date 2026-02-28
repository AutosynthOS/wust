/// Experimental tail-call dispatch interpreter.
///
/// Uses Rust's `become` keyword (explicit tail calls, nightly-only) to
/// dispatch opcodes as a chain of tail-calls rather than a `loop { match }`
/// pattern. The hypothesis is that tail-call dispatch gives each opcode
/// handler its own indirect call site, improving branch predictor accuracy
/// compared to a single centralized match-loop.
///
/// Only the opcodes needed for fib(30) are implemented. All others trap
/// with `Unimplemented`.
///
/// # Why flat parameters instead of a struct
///
/// The `become` keyword currently ICEs on arguments passed via
/// `PassMode::Indirect` (i.e., structs too large for registers). We work
/// around this by passing all state as individual scalar parameters. This
/// is ugly but necessary until the compiler supports indirect tail calls.
use crate::Module;
use crate::parse::body::{Block, InlineOp, OpCode};
use crate::parse::func::ParsedFunction;
use crate::stack::Stack;

use super::exec_recursive::{Frame, Trap};

const MAX_CALL_DEPTH: u32 = 10_000;

/// Set up a frame and execute a function using tail-call dispatch.
pub(crate) fn call_function_tc(
    module: &Module,
    stack: &mut Stack,
    func: &ParsedFunction,
    fuel: &mut i64,
    depth: &mut u32,
) -> Result<(), Trap> {
    *depth += 1;
    if *depth > MAX_CALL_DEPTH {
        *depth -= 1;
        return Err(Trap::CallStackExhausted);
    }

    let base = stack.base();
    let sp_offset = stack.sp();

    let return_sp = unsafe { base.add(sp_offset - func.arg_byte_count) };
    let locals = return_sp;

    unsafe {
        std::ptr::write_bytes(base.add(sp_offset), 0, func.extra_local_bytes);
    }
    stack.set_sp(sp_offset + func.extra_local_bytes);

    let frame = Frame {
        return_sp,
        locals,
        result_count: func.result_count,
    };

    let ops = func.body.ops.as_ptr();
    let blocks = func.body.blocks.as_ptr();
    let sp: *mut u8 = unsafe { base.add(stack.sp()) };
    let operand_base = unsafe { locals.add(func.arg_byte_count + func.extra_local_bytes) };

    let result = dispatch(
        module as *const Module,
        func as *const ParsedFunction,
        stack as *mut Stack,
        &frame as *const Frame,
        fuel as *mut i64,
        depth as *mut u32,
        ops,
        blocks,
        base,
        sp,
        locals,
        operand_base,
        0,
        0,
    );
    *depth -= 1;
    result
}

/// Fetch the next opcode and tail-call into its handler.
fn dispatch(
    module: *const Module,
    func: *const ParsedFunction,
    stack: *mut Stack,
    frame: *const Frame,
    fuel: *mut i64,
    depth: *mut u32,
    ops: *const InlineOp,
    blocks: *const Block,
    base: *mut u8,
    sp: *mut u8,
    locals: *mut u8,
    operand_base: *mut u8,
    pc: usize,
    _entry_bits: u64,
) -> Result<(), Trap> {
    unsafe { *fuel -= 1 };
    if unsafe { *fuel } < 0 {
        unsafe { (*stack).set_sp(sp.offset_from(base) as usize) };
        return Err(Trap::OutOfFuel);
    }

    let entry = unsafe { *ops.add(pc) };
    let entry_bits = entry.raw();
    let next_pc = pc + 1;

    match entry.opcode() {
        OpCode::Nop | OpCode::Block | OpCode::Loop => {
            become dispatch(module, func, stack, frame, fuel, depth, ops, blocks, base, sp, locals, operand_base, next_pc, entry_bits)
        }
        OpCode::Return => {
            become op_return(module, func, stack, frame, fuel, depth, ops, blocks, base, sp, locals, operand_base, next_pc, entry_bits)
        }
        OpCode::End => {
            become op_end(module, func, stack, frame, fuel, depth, ops, blocks, base, sp, locals, operand_base, next_pc, entry_bits)
        }
        OpCode::If => {
            become op_if(module, func, stack, frame, fuel, depth, ops, blocks, base, sp, locals, operand_base, next_pc, entry_bits)
        }
        OpCode::Else => {
            become op_else(module, func, stack, frame, fuel, depth, ops, blocks, base, sp, locals, operand_base, next_pc, entry_bits)
        }
        OpCode::I32Const => {
            become op_i32_const(module, func, stack, frame, fuel, depth, ops, blocks, base, sp, locals, operand_base, next_pc, entry_bits)
        }
        OpCode::I32Add => {
            become op_i32_add(module, func, stack, frame, fuel, depth, ops, blocks, base, sp, locals, operand_base, next_pc, entry_bits)
        }
        OpCode::I32Sub => {
            become op_i32_sub(module, func, stack, frame, fuel, depth, ops, blocks, base, sp, locals, operand_base, next_pc, entry_bits)
        }
        OpCode::I32LeS => {
            become op_i32_le_s(module, func, stack, frame, fuel, depth, ops, blocks, base, sp, locals, operand_base, next_pc, entry_bits)
        }
        OpCode::LocalGet => {
            become op_local_get(module, func, stack, frame, fuel, depth, ops, blocks, base, sp, locals, operand_base, next_pc, entry_bits)
        }
        OpCode::LocalSet => {
            become op_local_set(module, func, stack, frame, fuel, depth, ops, blocks, base, sp, locals, operand_base, next_pc, entry_bits)
        }
        OpCode::Call => {
            become op_call(module, func, stack, frame, fuel, depth, ops, blocks, base, sp, locals, operand_base, next_pc, entry_bits)
        }
        OpCode::LocalGetI32ConstLeSIf => {
            become op_local_get_i32_const_le_s_if(module, func, stack, frame, fuel, depth, ops, blocks, base, sp, locals, operand_base, next_pc, entry_bits)
        }
        OpCode::LocalGetReturn => {
            become op_local_get_return(module, func, stack, frame, fuel, depth, ops, blocks, base, sp, locals, operand_base, next_pc, entry_bits)
        }
        OpCode::LocalGetI32ConstSub => {
            become op_local_get_i32_const_sub(module, func, stack, frame, fuel, depth, ops, blocks, base, sp, locals, operand_base, next_pc, entry_bits)
        }
        OpCode::CallLocalSet => {
            become op_call_local_set(module, func, stack, frame, fuel, depth, ops, blocks, base, sp, locals, operand_base, next_pc, entry_bits)
        }
        OpCode::LocalGetLocalGetAdd => {
            become op_local_get_local_get_add(module, func, stack, frame, fuel, depth, ops, blocks, base, sp, locals, operand_base, next_pc, entry_bits)
        }
        other => {
            unsafe { (*stack).set_sp(sp.offset_from(base) as usize) };
            Err(Trap::Unimplemented(other))
        }
    }
}

// ---------------------------------------------------------------------------
// Opcode handlers
//
// Each handler has the same signature as `dispatch` so `become` works.
// Handlers that continue execution end with `become dispatch(...)`.
// Handlers that terminate call `finalize_return`.
// ---------------------------------------------------------------------------

/// Helper: reconstruct InlineOp from raw bits.
#[inline(always)]
fn entry_from(entry_bits: u64) -> InlineOp {
    InlineOp::from_raw(entry_bits)
}

fn op_return(
    _module: *const Module, _func: *const ParsedFunction, stack: *mut Stack,
    frame: *const Frame, _fuel: *mut i64, _depth: *mut u32,
    _ops: *const InlineOp, _blocks: *const Block, base: *mut u8,
    sp: *mut u8, _locals: *mut u8, _operand_base: *mut u8,
    _pc: usize, _entry_bits: u64,
) -> Result<(), Trap> {
    finalize_return(stack, frame, base, sp)
}

fn op_end(
    module: *const Module, func: *const ParsedFunction, stack: *mut Stack,
    frame: *const Frame, fuel: *mut i64, depth: *mut u32,
    ops: *const InlineOp, blocks: *const Block, base: *mut u8,
    sp: *mut u8, locals: *mut u8, operand_base: *mut u8,
    pc: usize, entry_bits: u64,
) -> Result<(), Trap> {
    let imm = entry_from(entry_bits).immediate_u32();
    if imm == 0 {
        return finalize_return(stack, frame, base, sp);
    }
    become dispatch(module, func, stack, frame, fuel, depth, ops, blocks, base, sp, locals, operand_base, pc, entry_bits)
}

fn op_if(
    module: *const Module, func: *const ParsedFunction, stack: *mut Stack,
    frame: *const Frame, fuel: *mut i64, depth: *mut u32,
    ops: *const InlineOp, blocks: *const Block, base: *mut u8,
    sp: *mut u8, locals: *mut u8, operand_base: *mut u8,
    pc: usize, entry_bits: u64,
) -> Result<(), Trap> {
    let imm = entry_from(entry_bits).immediate_u32();
    let sp = unsafe { sp.sub(8) };
    let condition = unsafe { *(sp as *const i32) };
    let pc = if condition == 0 {
        let block = unsafe { &*blocks.add(imm as usize) };
        if block.else_pc != 0 {
            block.else_pc as usize + 1
        } else {
            block.end_pc as usize + 1
        }
    } else {
        pc
    };
    become dispatch(module, func, stack, frame, fuel, depth, ops, blocks, base, sp, locals, operand_base, pc, entry_bits)
}

fn op_else(
    module: *const Module, func: *const ParsedFunction, stack: *mut Stack,
    frame: *const Frame, fuel: *mut i64, depth: *mut u32,
    ops: *const InlineOp, blocks: *const Block, base: *mut u8,
    sp: *mut u8, locals: *mut u8, operand_base: *mut u8,
    _pc: usize, entry_bits: u64,
) -> Result<(), Trap> {
    let imm = entry_from(entry_bits).immediate_u32();
    let block = unsafe { &*blocks.add(imm as usize) };
    let pc = block.end_pc as usize + 1;
    become dispatch(module, func, stack, frame, fuel, depth, ops, blocks, base, sp, locals, operand_base, pc, entry_bits)
}

fn op_i32_const(
    module: *const Module, func: *const ParsedFunction, stack: *mut Stack,
    frame: *const Frame, fuel: *mut i64, depth: *mut u32,
    ops: *const InlineOp, blocks: *const Block, base: *mut u8,
    sp: *mut u8, locals: *mut u8, operand_base: *mut u8,
    pc: usize, entry_bits: u64,
) -> Result<(), Trap> {
    let imm = entry_from(entry_bits).immediate_u32();
    let val = ((imm as i32) << 8 >> 8) as u64;
    unsafe { *(sp as *mut u64) = val };
    let sp = unsafe { sp.add(8) };
    become dispatch(module, func, stack, frame, fuel, depth, ops, blocks, base, sp, locals, operand_base, pc, entry_bits)
}

fn op_i32_add(
    module: *const Module, func: *const ParsedFunction, stack: *mut Stack,
    frame: *const Frame, fuel: *mut i64, depth: *mut u32,
    ops: *const InlineOp, blocks: *const Block, base: *mut u8,
    sp: *mut u8, locals: *mut u8, operand_base: *mut u8,
    pc: usize, entry_bits: u64,
) -> Result<(), Trap> {
    let sp = unsafe { sp.sub(8) };
    unsafe {
        let b = *(sp as *const i32);
        let a = *(sp.sub(8) as *const i32);
        *(sp.sub(8) as *mut u64) = a.wrapping_add(b) as u64;
    }
    become dispatch(module, func, stack, frame, fuel, depth, ops, blocks, base, sp, locals, operand_base, pc, entry_bits)
}

fn op_i32_sub(
    module: *const Module, func: *const ParsedFunction, stack: *mut Stack,
    frame: *const Frame, fuel: *mut i64, depth: *mut u32,
    ops: *const InlineOp, blocks: *const Block, base: *mut u8,
    sp: *mut u8, locals: *mut u8, operand_base: *mut u8,
    pc: usize, entry_bits: u64,
) -> Result<(), Trap> {
    let sp = unsafe { sp.sub(8) };
    unsafe {
        let b = *(sp as *const i32);
        let a = *(sp.sub(8) as *const i32);
        *(sp.sub(8) as *mut u64) = a.wrapping_sub(b) as u64;
    }
    become dispatch(module, func, stack, frame, fuel, depth, ops, blocks, base, sp, locals, operand_base, pc, entry_bits)
}

fn op_i32_le_s(
    module: *const Module, func: *const ParsedFunction, stack: *mut Stack,
    frame: *const Frame, fuel: *mut i64, depth: *mut u32,
    ops: *const InlineOp, blocks: *const Block, base: *mut u8,
    sp: *mut u8, locals: *mut u8, operand_base: *mut u8,
    pc: usize, entry_bits: u64,
) -> Result<(), Trap> {
    let sp = unsafe { sp.sub(8) };
    unsafe {
        let b = *(sp as *const i32);
        let a = *(sp.sub(8) as *const i32);
        *(sp.sub(8) as *mut u64) = (a <= b) as u64;
    }
    become dispatch(module, func, stack, frame, fuel, depth, ops, blocks, base, sp, locals, operand_base, pc, entry_bits)
}

fn op_local_get(
    module: *const Module, func: *const ParsedFunction, stack: *mut Stack,
    frame: *const Frame, fuel: *mut i64, depth: *mut u32,
    ops: *const InlineOp, blocks: *const Block, base: *mut u8,
    sp: *mut u8, locals: *mut u8, operand_base: *mut u8,
    pc: usize, entry_bits: u64,
) -> Result<(), Trap> {
    let imm = entry_from(entry_bits).immediate_u32();
    let val = unsafe { *(locals.add((imm as usize) * 8) as *const u64) };
    unsafe { *(sp as *mut u64) = val };
    let sp = unsafe { sp.add(8) };
    become dispatch(module, func, stack, frame, fuel, depth, ops, blocks, base, sp, locals, operand_base, pc, entry_bits)
}

fn op_local_set(
    module: *const Module, func: *const ParsedFunction, stack: *mut Stack,
    frame: *const Frame, fuel: *mut i64, depth: *mut u32,
    ops: *const InlineOp, blocks: *const Block, base: *mut u8,
    sp: *mut u8, locals: *mut u8, operand_base: *mut u8,
    pc: usize, entry_bits: u64,
) -> Result<(), Trap> {
    let imm = entry_from(entry_bits).immediate_u32();
    let sp = unsafe { sp.sub(8) };
    let val = unsafe { *(sp as *const u64) };
    unsafe { *(locals.add((imm as usize) * 8) as *mut u64) = val };
    become dispatch(module, func, stack, frame, fuel, depth, ops, blocks, base, sp, locals, operand_base, pc, entry_bits)
}

fn op_call(
    module: *const Module, func: *const ParsedFunction, stack: *mut Stack,
    frame: *const Frame, fuel: *mut i64, depth: *mut u32,
    ops: *const InlineOp, blocks: *const Block, base: *mut u8,
    sp: *mut u8, locals: *mut u8, operand_base: *mut u8,
    pc: usize, entry_bits: u64,
) -> Result<(), Trap> {
    let imm = entry_from(entry_bits).immediate_u32();
    unsafe { (*stack).set_sp(sp.offset_from(base) as usize) };
    let callee = unsafe { (&(*module).funcs).get_unchecked(imm as usize) };
    call_function_tc(
        unsafe { &*module },
        unsafe { &mut *stack },
        callee,
        unsafe { &mut *fuel },
        unsafe { &mut *depth },
    )?;
    let sp = unsafe { base.add((*stack).sp()) };
    become dispatch(module, func, stack, frame, fuel, depth, ops, blocks, base, sp, locals, operand_base, pc, entry_bits)
}

// --- Superinstructions ---

fn op_local_get_i32_const_le_s_if(
    module: *const Module, func: *const ParsedFunction, stack: *mut Stack,
    frame: *const Frame, fuel: *mut i64, depth: *mut u32,
    ops: *const InlineOp, blocks: *const Block, base: *mut u8,
    sp: *mut u8, locals: *mut u8, operand_base: *mut u8,
    pc: usize, entry_bits: u64,
) -> Result<(), Trap> {
    let entry = entry_from(entry_bits);
    let local_idx = entry.imm_u8_a() as usize;
    let konst = entry.imm_u8_b() as i8 as i32;
    let block_idx = entry.imm_u8_c() as usize;
    let val = unsafe { *(locals.add(local_idx * 8) as *const i32) };
    let pc = if val > konst {
        let block = unsafe { &*blocks.add(block_idx) };
        if block.else_pc != 0 {
            block.else_pc as usize + 1
        } else {
            block.end_pc as usize + 1
        }
    } else {
        pc
    };
    become dispatch(module, func, stack, frame, fuel, depth, ops, blocks, base, sp, locals, operand_base, pc, entry_bits)
}

fn op_local_get_return(
    _module: *const Module, _func: *const ParsedFunction, stack: *mut Stack,
    frame: *const Frame, _fuel: *mut i64, _depth: *mut u32,
    _ops: *const InlineOp, _blocks: *const Block, base: *mut u8,
    sp: *mut u8, locals: *mut u8, _operand_base: *mut u8,
    _pc: usize, entry_bits: u64,
) -> Result<(), Trap> {
    let local_idx = entry_from(entry_bits).imm_u8_a() as usize;
    let val = unsafe { *(locals.add(local_idx * 8) as *const u64) };
    unsafe { *(sp as *mut u64) = val };
    let sp = unsafe { sp.add(8) };
    finalize_return(stack, frame, base, sp)
}

fn op_local_get_i32_const_sub(
    module: *const Module, func: *const ParsedFunction, stack: *mut Stack,
    frame: *const Frame, fuel: *mut i64, depth: *mut u32,
    ops: *const InlineOp, blocks: *const Block, base: *mut u8,
    sp: *mut u8, locals: *mut u8, operand_base: *mut u8,
    pc: usize, entry_bits: u64,
) -> Result<(), Trap> {
    let entry = entry_from(entry_bits);
    let local_idx = entry.imm_u8_a() as usize;
    let konst = entry.imm_i16_hi() as i32;
    let val = unsafe { *(locals.add(local_idx * 8) as *const i32) };
    unsafe { *(sp as *mut u64) = val.wrapping_sub(konst) as u64 };
    let sp = unsafe { sp.add(8) };
    become dispatch(module, func, stack, frame, fuel, depth, ops, blocks, base, sp, locals, operand_base, pc, entry_bits)
}

fn op_call_local_set(
    module: *const Module, func: *const ParsedFunction, stack: *mut Stack,
    frame: *const Frame, fuel: *mut i64, depth: *mut u32,
    ops: *const InlineOp, blocks: *const Block, base: *mut u8,
    sp: *mut u8, locals: *mut u8, operand_base: *mut u8,
    pc: usize, entry_bits: u64,
) -> Result<(), Trap> {
    let entry = entry_from(entry_bits);
    let func_idx = entry.imm_u16_lo() as usize;
    let local_idx = entry.imm_u8_c() as usize;
    unsafe { (*stack).set_sp(sp.offset_from(base) as usize) };
    let callee = unsafe { (&(*module).funcs).get_unchecked(func_idx) };
    call_function_tc(
        unsafe { &*module },
        unsafe { &mut *stack },
        callee,
        unsafe { &mut *fuel },
        unsafe { &mut *depth },
    )?;
    let sp = unsafe { base.add((*stack).sp()) };
    let sp = unsafe { sp.sub(8) };
    let result = unsafe { *(sp as *const u64) };
    unsafe { *(locals.add(local_idx * 8) as *mut u64) = result };
    become dispatch(module, func, stack, frame, fuel, depth, ops, blocks, base, sp, locals, operand_base, pc, entry_bits)
}

fn op_local_get_local_get_add(
    module: *const Module, func: *const ParsedFunction, stack: *mut Stack,
    frame: *const Frame, fuel: *mut i64, depth: *mut u32,
    ops: *const InlineOp, blocks: *const Block, base: *mut u8,
    sp: *mut u8, locals: *mut u8, operand_base: *mut u8,
    pc: usize, entry_bits: u64,
) -> Result<(), Trap> {
    let entry = entry_from(entry_bits);
    let a_idx = entry.imm_u8_a() as usize;
    let b_idx = entry.imm_u8_b() as usize;
    let a = unsafe { *(locals.add(a_idx * 8) as *const i32) };
    let b = unsafe { *(locals.add(b_idx * 8) as *const i32) };
    unsafe { *(sp as *mut u64) = a.wrapping_add(b) as u64 };
    let sp = unsafe { sp.add(8) };
    become dispatch(module, func, stack, frame, fuel, depth, ops, blocks, base, sp, locals, operand_base, pc, entry_bits)
}

// ---------------------------------------------------------------------------
// Return: copy results back to caller's frame and reset SP.
// ---------------------------------------------------------------------------

fn finalize_return(
    stack: *mut Stack,
    frame: *const Frame,
    base: *mut u8,
    sp: *mut u8,
) -> Result<(), Trap> {
    let frame = unsafe { &*frame };
    let count = frame.result_count as usize;
    let byte_count = count * 8;
    let src = unsafe { sp.sub(byte_count) };
    let dst = frame.return_sp;
    match count {
        0 => {}
        1 => unsafe {
            let val = *(src as *const u64);
            *(dst as *mut u64) = val;
        },
        _ => unsafe {
            std::ptr::copy(src, dst, byte_count);
        },
    }
    unsafe { (*stack).set_sp(dst.add(byte_count).offset_from(base) as usize) };
    Ok(())
}
