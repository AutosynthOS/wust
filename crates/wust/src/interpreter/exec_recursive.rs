use crate::Module;
use crate::parse::body::{Block, BlockKind, OpCode};
use crate::parse::func::ParsedFunction;
use crate::stack::Stack;

/// Trap reasons that can occur during execution.
/// Stack-allocated, no heap — keeps the hot loop cheap.
#[derive(Debug)]
pub(crate) enum Trap {
    Unreachable,
    OutOfFuel,
    CallStackExhausted,
    Unimplemented(OpCode),
}

/// Maximum call depth before trapping with `CallStackExhausted`.
const MAX_CALL_DEPTH: u32 = 1000;

impl std::fmt::Display for Trap {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Trap::Unreachable => write!(f, "unreachable executed"),
            Trap::OutOfFuel => write!(f, "out of fuel"),
            Trap::CallStackExhausted => write!(f, "call stack exhausted"),
            Trap::Unimplemented(op) => write!(f, "unimplemented opcode: {op:?}"),
        }
    }
}

impl std::error::Error for Trap {}

/// Per-call execution state — lives as Rust locals, not on the wasm stack.
pub(crate) struct Frame {
    /// Where to write results on return (absolute pointer).
    pub return_sp: *mut u8,
    /// Where locals start (absolute pointer).
    pub locals: *mut u8,
    /// Number of result values to copy on return.
    pub result_count: u32,
}

/// Set up a frame and execute a function. Used by both the host entry
/// point and the `call` opcode.
pub(crate) fn call_function(
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
    let sp = stack.sp();

    let return_sp = unsafe { base.add(sp - func.arg_byte_count) };
    let locals = return_sp;

    // Zero extra locals (beyond params) in bulk and bump SP.
    unsafe {
        std::ptr::write_bytes(base.add(sp), 0, func.extra_local_bytes);
    }
    stack.set_sp(sp + func.extra_local_bytes);

    let frame = Frame {
        return_sp,
        locals,
        result_count: func.result_count,
    };

    let result = execute(module, func, stack, &frame, fuel, depth);
    *depth -= 1;
    result
}

fn execute(
    module: &Module,
    func: &ParsedFunction,
    stack: &mut Stack,
    frame: &Frame,
    fuel: &mut i64,
    depth: &mut u32,
) -> Result<(), Trap> {
    let ops = func.body.ops.as_ptr();
    let blocks = func.body.blocks.as_ptr();
    let base = stack.base();
    let mut sp: *mut u8 = unsafe { base.add(stack.sp()) };
    let locals = frame.locals;
    let mut pc: usize = 0;

    loop {
        *fuel -= 1;
        if *fuel < 0 {
            stack.set_sp(unsafe { sp.offset_from(base) as usize });
            return Err(Trap::OutOfFuel);
        }

        let entry = unsafe { *ops.add(pc) };
        pc += 1;

        let opcode = entry.opcode();
        let imm = entry.immediate_u32();

        match opcode {
            OpCode::Nop | OpCode::Block | OpCode::Loop => {}

            OpCode::Unreachable => {
                stack.set_sp(unsafe { sp.offset_from(base) as usize });
                return Err(Trap::Unreachable);
            }

            OpCode::Return => break,

            OpCode::If => {
                sp = unsafe { sp.sub(8) };
                let condition = unsafe { *(sp as *const i32) };
                if condition == 0 {
                    let block = unsafe { &*blocks.add(imm as usize) };
                    if block.else_pc != 0 {
                        pc = block.else_pc as usize + 1;
                    } else {
                        pc = block.end_pc as usize + 1;
                    }
                }
            }

            OpCode::Else => {
                let block = unsafe { &*blocks.add(imm as usize) };
                pc = block.end_pc as usize + 1;
            }

            OpCode::End => {
                if imm == 0 {
                    break;
                }
            }

            OpCode::Br => {
                let block = unsafe { &*blocks.add(imm as usize) };
                pc = branch_target(block);
            }

            OpCode::BrIf => {
                sp = unsafe { sp.sub(8) };
                let condition = unsafe { *(sp as *const i32) };
                if condition != 0 {
                    let block = unsafe { &*blocks.add(imm as usize) };
                    pc = branch_target(block);
                }
            }

            OpCode::Call => {
                stack.set_sp(unsafe { sp.offset_from(base) as usize });
                let callee = unsafe { module.funcs.get_unchecked(imm as usize) };
                call_function(module, stack, callee, fuel, depth)?;
                sp = unsafe { base.add(stack.sp()) };
            }

            OpCode::I32Const => {
                let val = ((imm as i32) << 8 >> 8) as u64;
                unsafe { *(sp as *mut u64) = val };
                sp = unsafe { sp.add(8) };
            }

            OpCode::I32Add => {
                sp = unsafe { sp.sub(8) };
                unsafe {
                    let b = *(sp as *const i32);
                    let a = *(sp.sub(8) as *const i32);
                    *(sp.sub(8) as *mut u64) = a.wrapping_add(b) as u64;
                }
            }

            OpCode::I32Sub => {
                sp = unsafe { sp.sub(8) };
                unsafe {
                    let b = *(sp as *const i32);
                    let a = *(sp.sub(8) as *const i32);
                    *(sp.sub(8) as *mut u64) = a.wrapping_sub(b) as u64;
                }
            }

            OpCode::I32Eqz => {
                unsafe {
                    let a = *(sp.sub(8) as *const i32);
                    *(sp.sub(8) as *mut u64) = (a == 0) as u64;
                }
            }

            OpCode::I32LeS => {
                sp = unsafe { sp.sub(8) };
                unsafe {
                    let b = *(sp as *const i32);
                    let a = *(sp.sub(8) as *const i32);
                    *(sp.sub(8) as *mut u64) = (a <= b) as u64;
                }
            }

            OpCode::RefNull => {
                unsafe { *(sp as *mut u64) = 0 };
                sp = unsafe { sp.add(8) };
            }

            OpCode::LocalGet => {
                let val = unsafe { *(locals.add((imm as usize) * 8) as *const u64) };
                unsafe { *(sp as *mut u64) = val };
                sp = unsafe { sp.add(8) };
            }

            OpCode::LocalSet => {
                sp = unsafe { sp.sub(8) };
                let val = unsafe { *(sp as *const u64) };
                unsafe { *(locals.add((imm as usize) * 8) as *mut u64) = val };
            }

            OpCode::LocalTee => {
                let val = unsafe { *(sp.sub(8) as *const u64) };
                unsafe { *(locals.add((imm as usize) * 8) as *mut u64) = val };
            }

            // TODO: globals storage not implemented yet.
            OpCode::GlobalGet => {
                unsafe { *(sp as *mut u64) = 0 };
                sp = unsafe { sp.add(8) };
            }
            OpCode::GlobalSet => {
                sp = unsafe { sp.sub(8) };
            }

            OpCode::LocalGetI32ConstSub => {
                let local_idx = entry.imm_u8_a() as usize;
                let konst = entry.imm_i16_hi() as i32;
                let val = unsafe { *(locals.add(local_idx * 8) as *const i32) };
                unsafe { *(sp as *mut u64) = val.wrapping_sub(konst) as u64 };
                sp = unsafe { sp.add(8) };
            }

            OpCode::LocalGetI32ConstAdd => {
                let local_idx = entry.imm_u8_a() as usize;
                let konst = entry.imm_i16_hi() as i32;
                let val = unsafe { *(locals.add(local_idx * 8) as *const i32) };
                unsafe { *(sp as *mut u64) = val.wrapping_add(konst) as u64 };
                sp = unsafe { sp.add(8) };
            }

            OpCode::CallLocalSet => {
                let func_idx = entry.imm_u16_lo() as usize;
                let local_idx = entry.imm_u8_c() as usize;
                stack.set_sp(unsafe { sp.offset_from(base) as usize });
                let callee = unsafe { module.funcs.get_unchecked(func_idx) };
                call_function(module, stack, callee, fuel, depth)?;
                sp = unsafe { base.add(stack.sp()) };
                // Pop result into local.
                sp = unsafe { sp.sub(8) };
                let result = unsafe { *(sp as *const u64) };
                unsafe { *(locals.add(local_idx * 8) as *mut u64) = result };
            }

            OpCode::LocalGetLocalGetAdd => {
                let a_idx = entry.imm_u8_a() as usize;
                let b_idx = entry.imm_u8_b() as usize;
                let a = unsafe { *(locals.add(a_idx * 8) as *const i32) };
                let b = unsafe { *(locals.add(b_idx * 8) as *const i32) };
                unsafe { *(sp as *mut u64) = a.wrapping_add(b) as u64 };
                sp = unsafe { sp.add(8) };
            }

            OpCode::LocalGetReturn => {
                let local_idx = entry.imm_u8_a() as usize;
                let val = unsafe { *(locals.add(local_idx * 8) as *const u64) };
                unsafe { *(sp as *mut u64) = val };
                sp = unsafe { sp.add(8) };
                break;
            }

            OpCode::LocalGetI32ConstLeSIf => {
                let local_idx = entry.imm_u8_a() as usize;
                let konst = entry.imm_u8_b() as i8 as i32;
                let block_idx = entry.imm_u8_c() as usize;
                let val = unsafe { *(locals.add(local_idx * 8) as *const i32) };
                if val <= konst {
                    // Condition true: fall through into if-body.
                } else {
                    // Condition false: jump to else or end.
                    let block = unsafe { &*blocks.add(block_idx) };
                    if block.else_pc != 0 {
                        pc = block.else_pc as usize + 1;
                    } else {
                        pc = block.end_pc as usize + 1;
                    }
                }
            }

            OpCode::LocalGetI32EqzIf => {
                let local_idx = entry.imm_u8_a() as usize;
                let block_idx = entry.imm_u8_b() as usize;
                let val = unsafe { *(locals.add(local_idx * 8) as *const i32) };
                if val == 0 {
                    // eqz is true: fall through into if-body.
                } else {
                    // eqz is false: jump to else or end.
                    let block = unsafe { &*blocks.add(block_idx) };
                    if block.else_pc != 0 {
                        pc = block.else_pc as usize + 1;
                    } else {
                        pc = block.end_pc as usize + 1;
                    }
                }
            }

            _ => {
                stack.set_sp(unsafe { sp.offset_from(base) as usize });
                return Err(Trap::Unimplemented(opcode));
            }
        }
    }

    // Copy results and reset SP.
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
            // Use `copy` instead of `copy_nonoverlapping`: when a
            // function has zero args, src and dst can be the same address.
            std::ptr::copy(src, dst, byte_count);
        },
    }
    stack.set_sp(unsafe { dst.add(byte_count).offset_from(base) as usize });

    Ok(())
}

/// Resolve a branch target PC from a block.
/// Loop: back-edge to first instruction inside the loop (start_pc + 1).
/// Block/If/Function: forward to instruction after End (end_pc + 1).
fn branch_target(block: &Block) -> usize {
    if block.kind == BlockKind::Loop {
        block.start_pc as usize + 1
    } else {
        block.end_pc as usize + 1
    }
}
