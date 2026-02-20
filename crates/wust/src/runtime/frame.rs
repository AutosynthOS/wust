//! Call frame and label types for the interpreter.
//!
//! Contains the `Frame` and `Label` structs, frame lifecycle functions
//! (`new_frame`, `do_return`, `setup_local_call`), stack manipulation
//! (`stack_unwind`, `do_br`), and typed stack pop helpers.

use crate::runtime::exec::ExecError;
use crate::runtime::module::Module;
use crate::runtime::opcode::Op;
use crate::runtime::value::Value;

// TODO: tune once runtime is stable. Catches infinite loops during testing.
pub(crate) const MAX_STEPS: u64 = 1_000_000_000;
pub(crate) const MAX_CALL_DEPTH: usize = 10_000;

/// A single call frame in the interpreter.
///
/// Borrows the function body and branch tables from the `Module` so the
/// main loop can index into them without extra lookups.
pub(crate) struct Frame<'a> {
    pub(crate) pc: usize,
    /// Index into the shared `stack` where this frame's locals begin.
    pub(crate) locals_start: usize,
    /// The stack height when this frame was entered (after locals are allocated).
    pub(crate) stack_height: usize,
    /// Index into the shared `labels` vec where this frame's labels begin.
    pub(crate) labels_start: usize,
    pub(crate) arity: usize,
    pub(crate) body: &'a [Op],
    pub(crate) br_tables: &'a [(Vec<u32>, u32)],
}

/// A label in the control flow stack.
pub(crate) struct Label {
    pub(crate) target: usize,
    pub(crate) stack_height: usize,
    pub(crate) arity: usize,
    pub(crate) is_loop: bool,
}

// ---------------------------------------------------------------------------
// Typed stack pop helpers
// ---------------------------------------------------------------------------

#[inline(always)]
pub(crate) fn pop_raw(stack: &mut Vec<u64>) -> u64 {
    stack.pop().unwrap()
}

#[inline(always)]
pub(crate) fn pop_i32(stack: &mut Vec<u64>) -> i32 {
    stack.pop().unwrap() as i32
}

#[inline(always)]
pub(crate) fn pop_i64(stack: &mut Vec<u64>) -> i64 {
    stack.pop().unwrap() as i64
}

#[inline(always)]
pub(crate) fn pop_f32(stack: &mut Vec<u64>) -> f32 {
    f32::from_bits(stack.pop().unwrap() as u32)
}

#[inline(always)]
pub(crate) fn pop_f64(stack: &mut Vec<u64>) -> f64 {
    f64::from_bits(stack.pop().unwrap())
}

// ---------------------------------------------------------------------------
// Frame lifecycle
// ---------------------------------------------------------------------------

/// Push locals onto the shared stack (params from args, rest zeroed).
/// Returns the index into `stack` where locals start.
fn push_locals(stack: &mut Vec<u64>, func: &crate::runtime::module::Func, args: &[Value]) -> usize {
    let locals_start = stack.len();
    for (i, &_ty) in func.locals.iter().enumerate() {
        if i < args.len() {
            stack.push(args[i].to_bits());
        } else {
            stack.push(0u64);
        }
    }
    locals_start
}

pub(crate) fn new_frame<'a>(
    module: &'a Module,
    func_idx: u32,
    args: &[Value],
    stack: &mut Vec<u64>,
    labels: &mut Vec<Label>,
) -> Result<Frame<'a>, ExecError> {
    let func = module.get_func(func_idx)
        .ok_or_else(|| ExecError::NotFound(format!("function {func_idx} not found (import or invalid index)")))?;
    let func_type = module.types.get(func.type_idx as usize)
        .ok_or_else(|| ExecError::Trap(format!("type index {} out of bounds", func.type_idx)))?;
    let arity = func_type.results().len();
    let locals_start = push_locals(stack, func, args);
    let stack_height = stack.len();
    let labels_start = labels.len();
    labels.push(Label {
        target: func.body.len().saturating_sub(1),
        stack_height,
        arity,
        is_loop: false,
    });
    Ok(Frame {
        pc: 0,
        locals_start,
        stack_height,
        labels_start,
        arity,
        body: &func.body,
        br_tables: &func.br_tables,
    })
}

/// Handle returning from a frame: unwind the stack, move return values,
/// truncate labels. Returns `true` if the call stack is empty (final return).
pub(crate) fn do_return(
    frame: &Frame<'_>,
    stack: &mut Vec<u64>,
    labels: &mut Vec<Label>,
    call_stack: &mut Vec<Frame<'_>>,
) -> bool {
    // Unwind stack to frame's base, preserving return values
    stack_unwind(stack, frame.stack_height, frame.arity);
    // Now move results down over the locals area
    let arity = frame.arity;
    let results_start = stack.len() - arity;
    let locals_start = frame.locals_start;
    if arity > 0 && results_start > locals_start {
        stack.copy_within(results_start..results_start + arity, locals_start);
    }
    stack.truncate(locals_start + arity);
    // Clean up labels
    labels.truncate(frame.labels_start);
    call_stack.is_empty()
}

/// Set up a local (non-import) call: extend stack with zero locals, push label, swap frame.
pub(crate) fn setup_local_call<'a>(
    frame: &mut Frame<'a>,
    call_stack: &mut Vec<Frame<'a>>,
    stack: &mut Vec<u64>,
    labels: &mut Vec<Label>,
    callee: &'a crate::runtime::module::Func,
    callee_type: &wasmparser::FuncType,
) -> Result<(), ExecError> {
    let param_count = callee_type.params().len();
    let new_arity = callee_type.results().len();
    let locals_start = stack.len() - param_count;
    let extra_locals = callee.locals.len() - param_count;
    for _ in 0..extra_locals {
        stack.push(0u64);
    }
    let stack_height = stack.len();
    let labels_start = labels.len();
    labels.push(Label {
        target: callee.body.len().saturating_sub(1),
        stack_height,
        arity: new_arity,
        is_loop: false,
    });
    let new_f = Frame {
        pc: 0,
        locals_start,
        stack_height,
        labels_start,
        arity: new_arity,
        body: &callee.body,
        br_tables: &callee.br_tables,
    };
    if call_stack.len() >= MAX_CALL_DEPTH {
        return Err(ExecError::Trap("call stack exhausted".into()));
    }
    let old_frame = std::mem::replace(frame, new_f);
    call_stack.push(old_frame);
    Ok(())
}

// ---------------------------------------------------------------------------
// Stack manipulation
// ---------------------------------------------------------------------------

/// Truncate stack to `height`, preserving the top `arity` values.
/// Avoids Vec allocation by doing an in-place copy.
#[inline(always)]
pub(crate) fn stack_unwind(stack: &mut Vec<u64>, height: usize, arity: usize) {
    if arity == 0 {
        stack.truncate(height);
    } else if stack.len() - arity > height {
        // Copy results down in-place
        let src = stack.len() - arity;
        stack.copy_within(src.., height);
        stack.truncate(height + arity);
    }
    // else: stack is already at the right height, nothing to do
}

/// Handle a branch instruction: unwind the stack to the label, jump to target.
pub(crate) fn do_br(frame: &mut Frame, stack: &mut Vec<u64>, labels: &mut Vec<Label>, depth: u32, steps: &mut u64) -> Result<(), ExecError> {
    let label_idx = labels.len() - 1 - depth as usize;
    let label = &labels[label_idx];

    let arity = label.arity;
    let sh = label.stack_height;
    let is_loop = label.is_loop;
    let target = label.target;

    stack_unwind(stack, sh, arity);
    if is_loop {
        // Backward branch — check execution limit
        *steps += 1;
        // Step limit disabled for now — re-enable when needed
        // if *steps > MAX_STEPS {
        //     return Err(ExecError::execution_limit());
        // }
        labels.truncate(label_idx + 1);
        frame.pc = target + 1;
    } else {
        labels.truncate(label_idx);
        frame.pc = target + 1;
    }
    Ok(())
}
