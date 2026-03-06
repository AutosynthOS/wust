#[cfg(test)]
mod tests;

use wasmparser::ValType;

use crate::module::body::Block;
use crate::module::op::{InlineOp, OpCode};
use crate::task::frame::FrameHeader;
use crate::task::{Outcome, Task, WasmFramePointer};
use crate::{BlockKind, FRAME_HEADER_SIZE, FuncIdx, FuncMeta};

use super::ModuleExecutor;

/// Canonical stack-based interpreter — the correctness oracle.
///
/// No optimizations, no fusing. Executes the `InlineOp` stream
/// directly against the universal stack ABI.
pub struct Interpreter;

impl ModuleExecutor for Interpreter {
    fn poll(&self, task: &mut Task) -> Outcome {
        let funcs = &task.module.funcs;
        let fuel = &mut task.context.fuel;
        let wasm_fp = &mut task.context.wasm_fp;
        let base = wasm_fp.base();

        let outcome = loop {
            let func = &funcs[*wasm_fp.frame().func_idx as usize];
            let fp = wasm_fp.ptr;

            let pc = wasm_fp.frame().resume_pc;

            let mut stack = StackMachine {
                ops: func.body.ops.as_ptr(),
                blocks: func.body.blocks.as_ptr(),
                wasm_fp,
                sp: unsafe { fp.add(func.body.operand_depth[pc as usize] as usize * 4) },
                #[cfg(debug_assertions)]
                depths: func.body.operand_depth.as_ptr(),
                funcs,
                fuel,
            };

            match step(&mut stack, pc) {
                Outcome::Call => continue,
                Outcome::Return => {
                    // if our fp is at base, we've returned all the way
                    // to the outermost frame, which is the end of
                    // the program
                    if wasm_fp.ptr == base {
                        break Outcome::Return;
                    }
                }
                outcome => break outcome,
            }
        };
        task.context.outcome = outcome;
        outcome
    }
}

/// All mutable interpreter state for a single function invocation.
///
/// Owns the operand stack pointer (`sp`), instruction stream pointers,
/// and the frame pointer for local access. Initialized once per `poll()`
/// and threaded through `step()` tail calls.
struct StackMachine<'a> {
    ops: *const InlineOp,
    blocks: *const Block,
    wasm_fp: &'a mut WasmFramePointer,
    /// Operand stack pointer — the next free slot.
    sp: *mut u8,
    #[cfg(debug_assertions)]
    depths: *const u16,
    funcs: &'a [FuncMeta],
    fuel: &'a mut i64,
}

impl StackMachine<'_> {
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
        unsafe { (self.wasm_fp.ptr.sub(fp_offset as usize) as *const i32).read_unaligned() }
    }

    fn write_i32(&self, fp_offset: u32, val: i32) {
        unsafe { (self.wasm_fp.ptr.sub(fp_offset as usize) as *mut i32).write_unaligned(val) }
    }

    fn read_i64(&self, fp_offset: u32) -> i64 {
        unsafe { (self.wasm_fp.ptr.sub(fp_offset as usize) as *const i64).read_unaligned() }
    }

    fn write_i64(&self, fp_offset: u32, val: i64) {
        unsafe { (self.wasm_fp.ptr.sub(fp_offset as usize) as *mut i64).write_unaligned(val) }
    }

    /// Push a new frame onto the stack.
    ///
    /// Writes a FrameHeader at `self.sp` and advances fp to `self.sp + HEADER_SIZE`.
    /// The new fp becomes the operand base for the callee.
    pub fn push_frame(&mut self, func_idx: FuncIdx, resume_pc: u32) {
        // Save caller's resume point in caller's own header.
        self.wasm_fp.frame_mut().resume_pc = resume_pc;

        let new_fp = unsafe { self.sp.add(FRAME_HEADER_SIZE) };
        let prev_fp_offset = new_fp as usize - self.wasm_fp.ptr as usize;

        let frame = FrameHeader::new(func_idx, 0, prev_fp_offset as u32);

        unsafe {
            *(self.sp as *mut FrameHeader) = frame;
        }

        self.wasm_fp.ptr = new_fp;
        self.sp = new_fp;
    }

    /// Pop the current frame, copying results back to the caller's
    /// operand stack position.
    ///
    /// 1. Read header (func_idx → locals_size, results_size, prev_fp_offset)
    /// 2. dest = fp - HEADER_SIZE - locals_size (start of this frame's params)
    /// 3. Copy results from (sp - results_size) to dest
    /// 4. sp = dest + results_size
    /// 5. Restore fp via prev_fp_offset (if not outermost)
    fn pop_frame_with_results(&mut self) {
        let header = *self.wasm_fp.frame();
        let func = &self.funcs[*header.func_idx as usize];
        let results_size = func.results_size() as usize;
        let locals_size = func.locals_size as usize;

        let dest = unsafe { self.wasm_fp.ptr.sub(FRAME_HEADER_SIZE + locals_size) };
        let src = unsafe { self.sp.sub(results_size) };

        unsafe { std::ptr::copy(src, dest, results_size) };

        self.sp = unsafe { dest.add(results_size) };

        self.wasm_fp.ptr = unsafe { self.wasm_fp.ptr.sub(header.prev_fp_offset as usize) };
    }
}

fn step(m: &mut StackMachine, pc: u32) -> Outcome {
    #[cfg(debug_assertions)]
    debug_assert_eq!(
        m.sp as usize - m.wasm_fp.ptr as usize,
        unsafe { *m.depths.add(pc as usize) } as usize * 4,
        "sp drift at pc={pc}"
    );

    // Fuel check: decrement and suspend if exhausted.
    // Use < 0 so fuel=1 executes one instruction before suspending:
    // fuel=1 → decrement to 0 → execute → next step → decrement to -1 → suspend.
    *m.fuel -= 1;
    if *m.fuel < 0 {
        m.wasm_fp.frame_mut().resume_pc = pc;
        return Outcome::Suspended;
    }

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
            let val = m.read_i32(op.local_byte_offset());
            m.push_i32(val);
        }
        OpCode::LocalSetI32 => {
            let val = m.pop_i32();
            m.write_i32(op.local_byte_offset(), val);
        }
        OpCode::LocalTeeI32 => {
            let val = m.peek_i32();
            m.write_i32(op.local_byte_offset(), val);
        }
        OpCode::LocalGetI64 => {
            let val = m.read_i64(op.local_byte_offset());
            m.push_i64(val);
        }
        OpCode::LocalSetI64 => {
            let val = m.pop_i64();
            m.write_i64(op.local_byte_offset(), val);
        }
        OpCode::LocalTeeI64 => {
            let val = m.peek_i64();
            m.write_i64(op.local_byte_offset(), val);
        }
        OpCode::If => {
            let cond = m.pop_i32();
            if cond == 0 {
                let block = unsafe { &*m.blocks.add(op.immediate_u32() as usize) };
                let target = if block.else_pc != 0 {
                    block.else_pc + 1
                } else {
                    block.end_pc + 1
                };
                become step(m, target);
            }
        }
        OpCode::Call => {
            let func_idx = FuncIdx::new(op.immediate_u32());
            let func = &m.funcs[*func_idx as usize];
            // locals should be in place, we just want to push
            // zero'd locals onto the stack for the callee
            let mut iterator = func.locals.iter();
            while let Some(ty) = iterator.next() {
                match ty {
                    ValType::I32 => m.push_i32(0),
                    ValType::I64 => m.push_i64(0),
                    _ => todo!("local type {:?}", ty),
                }
            }
            m.push_frame(func_idx, pc + 1);

            return Outcome::Call;
        }
        OpCode::End => {
            let block = unsafe { &*m.blocks.add(op.immediate_u32() as usize) };

            if block.kind == BlockKind::Function {
                // pop our current frame
                m.pop_frame_with_results();
                return Outcome::Return;
            }
        }

        OpCode::Return => {
            // pop our current frame
            m.pop_frame_with_results();
            return Outcome::Return;
        }
        _ => todo!("opcode {:?}", op.opcode()),
    }

    become step(m, pc + 1);
}
