use crate::module::op::{InlineOp, OpCode};
use crate::task::frame::FRAME_HEADER_SIZE;
use crate::task::{Outcome, Task};

use super::ModuleExecutor;

/// Canonical stack-based interpreter — the correctness oracle.
///
/// No optimizations, no fusing. Executes the `InlineOp` stream
/// directly against the universal stack ABI.
pub struct Interpreter;

impl ModuleExecutor for Interpreter {
    fn poll(&self, task: &mut Task) -> Outcome {
        let fp = task.context.wasm_fp.ptr;
        let header = unsafe { &*(fp as *const crate::task::frame::FrameHeader) };
        let func = &task.module.funcs[*header.func_idx() as usize];
        let stack_base = unsafe { fp.add(FRAME_HEADER_SIZE + func.locals_size as usize) };

        let mut stack = StackMachine {
            ops: func.body.ops.as_ptr(),
            fp,
            sp: stack_base,
            #[cfg(debug_assertions)]
            depths: func.body.operand_depth.as_ptr(),
            #[cfg(debug_assertions)]
            stack_base,
        };

        let outcome = step(&mut stack, 0);
        task.context.outcome = outcome;
        outcome
    }
}

/// All mutable interpreter state for a single function invocation.
///
/// Owns the operand stack pointer (`sp`), instruction stream pointers,
/// and the frame pointer for local access. Initialized once per `poll()`
/// and threaded through `step()` tail calls.
struct StackMachine {
    ops: *const InlineOp,
    /// Frame pointer — points at the FrameHeader.
    fp: *mut u8,
    /// Operand stack pointer — the next free slot.
    sp: *mut u8,
    /// Debug-only: operand depth side table and stack base for drift checks.
    #[cfg(debug_assertions)]
    depths: *const u16,
    #[cfg(debug_assertions)]
    stack_base: *mut u8,
}

impl StackMachine {
    // --- operand stack ---

    fn pop_i32(&mut self) -> i32 {
        self.sp = unsafe { self.sp.sub(4) };
        unsafe { (self.sp as *const i32).read_unaligned() }
    }

    fn push_i32(&mut self, val: i32) {
        unsafe { (self.sp as *mut i32).write_unaligned(val) };
        self.sp = unsafe { self.sp.add(4) };
    }

    fn pop_i64(&mut self) -> i64 {
        self.sp = unsafe { self.sp.sub(8) };
        unsafe { (self.sp as *const i64).read_unaligned() }
    }

    fn push_i64(&mut self, val: i64) {
        unsafe { (self.sp as *mut i64).write_unaligned(val) };
        self.sp = unsafe { self.sp.add(8) };
    }

    fn peek_i32(&self) -> i32 {
        unsafe { (self.sp.sub(4) as *const i32).read_unaligned() }
    }

    fn peek_i64(&self) -> i64 {
        unsafe { (self.sp.sub(8) as *const i64).read_unaligned() }
    }

    // --- frame-relative access (locals) ---

    fn read_i32(&self, fp_offset: u32) -> i32 {
        unsafe { (self.fp.add(fp_offset as usize) as *const i32).read_unaligned() }
    }

    fn write_i32(&self, fp_offset: u32, val: i32) {
        unsafe { (self.fp.add(fp_offset as usize) as *mut i32).write_unaligned(val) }
    }

    fn read_i64(&self, fp_offset: u32) -> i64 {
        unsafe { (self.fp.add(fp_offset as usize) as *const i64).read_unaligned() }
    }

    fn write_i64(&self, fp_offset: u32, val: i64) {
        unsafe { (self.fp.add(fp_offset as usize) as *mut i64).write_unaligned(val) }
    }
}

fn step(m: &mut StackMachine, pc: u32) -> Outcome {
    #[cfg(debug_assertions)]
    debug_assert_eq!(
        m.sp as usize - m.stack_base as usize,
        unsafe { *m.depths.add(pc as usize) } as usize * 4,
        "sp drift at pc={pc}"
    );

    let op = unsafe { *m.ops.add(pc as usize) };

    match op.opcode() {
        OpCode::I32Const => {
            m.push_i32(op.immediate_i32());
        }
        OpCode::I32Add => {
            let b = m.pop_i32();
            let a = m.pop_i32();
            m.push_i32(a.wrapping_add(b));
        }
        OpCode::I32Sub => {
            let b = m.pop_i32();
            let a = m.pop_i32();
            m.push_i32(a.wrapping_sub(b));
        }
        OpCode::I32LeS => {
            let b = m.pop_i32();
            let a = m.pop_i32();
            m.push_i32((a <= b) as i32);
        }
        OpCode::LocalGetI32 => {
            let val = m.read_i32(op.immediate_u32());
            m.push_i32(val);
        }
        OpCode::LocalSetI32 => {
            let val = m.pop_i32();
            m.write_i32(op.immediate_u32(), val);
        }
        OpCode::LocalTeeI32 => {
            let val = m.peek_i32();
            m.write_i32(op.immediate_u32(), val);
        }
        OpCode::LocalGetI64 => {
            let val = m.read_i64(op.immediate_u32());
            m.push_i64(val);
        }
        OpCode::LocalSetI64 => {
            let val = m.pop_i64();
            m.write_i64(op.immediate_u32(), val);
        }
        OpCode::LocalTeeI64 => {
            let val = m.peek_i64();
            m.write_i64(op.immediate_u32(), val);
        }
        OpCode::End => {
            return Outcome::Return;
        }
        _ => todo!("opcode {:?}", op.opcode()),
    }

    become step(m, pc + 1);
}

#[cfg(test)]
mod tests;
