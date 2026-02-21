use crate::parse::body::{InlineOp, OpCode};
use crate::parse::func::ParsedFunction;
use crate::stack::Stack;

/// Whether the interpreter should continue or stop.
enum Step {
    Continue,
    End,
}

pub(crate) fn execute(func: &ParsedFunction, stack: &mut Stack) -> Result<(), anyhow::Error> {
    let mut pc: usize = 0;

    loop {
        if pc >= func.body.ops.len() {
            break;
        }

        let entry = func.body.ops[pc];
        pc += 1;

        match step(entry, stack)? {
            Step::Continue => {}
            Step::End => break,
        }
    }

    Ok(())
}

/// Dispatch a single instruction. Always inlined for tight loop performance.
#[inline(always)]
fn step(op: InlineOp, stack: &mut Stack) -> Result<Step, anyhow::Error> {
    let opcode = op.opcode();
    let imm = op.immediate().value();

    match opcode {
        OpCode::Nop => {}

        OpCode::Unreachable => {
            anyhow::bail!("unreachable executed");
        }

        OpCode::End => return Ok(Step::End),

        OpCode::Return => return Ok(Step::End),

        OpCode::I32Const => {
            // Sign-extend 24-bit immediate to i32.
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

        _ => {
            // Not yet implemented — skip.
        }
    }

    Ok(Step::Continue)
}
