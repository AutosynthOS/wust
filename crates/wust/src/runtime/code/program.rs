//! Program execution types and entry points.
//!
//! Contains the control flow structs, stack pop helpers, branch/return
//! helpers, and the public `call`/`invoke` entry points that set up
//! the mmap'd stack and delegate to the interpreter loop in `exec.rs`.

use super::stack::Stack;
use crate::runtime::error::ExecError;
use crate::runtime::module::Module;
use crate::runtime::store::Store;
use crate::runtime::value::Value;

/// Lightweight control stack entry for block/loop/if tracking.
///
/// Stores just enough info for `br` to unwind the operand stack and jump.
pub(crate) struct ControlEntry {
    /// Stack byte offset to unwind to on `br`.
    pub return_sp: u32,
    /// Branch target PC. For blocks: end_pc. For loops: pc past OP_LOOP.
    pub target_pc: usize,
    /// Number of result values to preserve on `br` (in u64 slots).
    pub arity: usize,
    /// True for loops (br jumps backward), false for blocks (br jumps forward).
    pub is_loop: bool,
}

/// Saved caller state pushed on function call, popped on return.
///
/// No borrowed references — just indices that re-derive the function on restore.
pub(crate) struct CallFrame {
    pub func_idx: u32,
    pub pc: usize,
    pub locals_sp: u32,
    pub controls_start: usize,
}

// ---------------------------------------------------------------------------
// Pop helpers — all values stored as u64 (8-byte slots).
// ---------------------------------------------------------------------------

#[inline(always)]
pub(crate) unsafe fn pop_i32(stack: &mut Stack) -> i32 {
    unsafe { stack.pop_u64() as u32 as i32 }
}

#[inline(always)]
pub(crate) unsafe fn pop_i64(stack: &mut Stack) -> i64 {
    unsafe { stack.pop_u64() as i64 }
}

#[inline(always)]
pub(crate) unsafe fn pop_f32(stack: &mut Stack) -> f32 {
    unsafe { f32::from_bits(stack.pop_u64() as u32) }
}

#[inline(always)]
pub(crate) unsafe fn pop_f64(stack: &mut Stack) -> f64 {
    unsafe { f64::from_bits(stack.pop_u64()) }
}

#[inline(always)]
pub(crate) unsafe fn pop_raw(stack: &mut Stack) -> u64 {
    unsafe { stack.pop_u64() }
}

// ---------------------------------------------------------------------------
// Host function call helper
// ---------------------------------------------------------------------------

/// Pop params from the unified stack, call a host function, push results.
pub(crate) unsafe fn call_host(
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
        .map(|(i, &ty)| unsafe { Value::from_bits(stack.read_u64(base + i as u32 * 8), ty) })
        .collect();
    unsafe { stack.set_sp(base) };
    let results = host_fn(&args, memory).map_err(|e| ExecError::Trap(format!("trap: {e}")))?;
    for r in results {
        unsafe { stack.push_u64(r.to_bits()) };
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Branch helper
// ---------------------------------------------------------------------------

/// Execute a `br` instruction targeting the control entry at `depth`.
///
/// For blocks: preserves `arity` result values, unwinds the operand
/// stack to `return_sp`, pushes results, jumps to `target_pc + 1`.
///
/// For loops: unwinds the operand stack to `return_sp`, jumps to
/// `target_pc` (past the OP_LOOP instruction).
#[inline(always)]
pub(crate) unsafe fn do_br(
    stack: &mut Stack,
    controls: &mut Vec<ControlEntry>,
    depth: u32,
    pc: &mut usize,
) {
    let idx = controls.len() - 1 - depth as usize;
    let entry = &controls[idx];

    if entry.is_loop {
        let arity = entry.arity;
        let return_sp = entry.return_sp;

        // Preserve loop params: copy top `arity` values to return_sp.
        let results_start = stack.sp() - arity as u32 * 8;
        unsafe {
            for i in 0..arity as u32 {
                let val = stack.read_u64(results_start + i * 8);
                stack.write_u64(return_sp + i * 8, val);
            }
            stack.set_sp(return_sp + arity as u32 * 8);
        }
        *pc = entry.target_pc;
        // Keep the loop's control entry for re-entry
        controls.truncate(idx + 1);
    } else {
        let arity = entry.arity;
        let return_sp = entry.return_sp;
        let target_pc = entry.target_pc;

        // Move result values in-place from stack top to return_sp.
        let results_start = stack.sp() - arity as u32 * 8;
        unsafe {
            for i in 0..arity as u32 {
                let val = stack.read_u64(results_start + i * 8);
                stack.write_u64(return_sp + i * 8, val);
            }
            stack.set_sp(return_sp + arity as u32 * 8);
        }
        *pc = target_pc + 1;
        // Remove the target block's entry (and everything above it)
        controls.truncate(idx);
    }
}

// ---------------------------------------------------------------------------
// Return helper
// ---------------------------------------------------------------------------

/// Execute a function return. Unwinds the stack past callee's locals,
/// pushes result values onto the caller's operand stack.
///
/// Returns `true` if this was the top-level return (back to Rust).
#[inline(always)]
pub(crate) unsafe fn do_return(
    stack: &mut Stack,
    call_frames: &mut Vec<CallFrame>,
    controls: &mut Vec<ControlEntry>,
    module: &Module,
    current_func_idx: u32,
    current_locals_sp: u32,
    current_controls_start: usize,
) -> bool {
    let func_type_idx = module.func_types[current_func_idx as usize];
    let func_type = &module.types[func_type_idx as usize];
    let result_count = func_type.results().len();

    let results_start = stack.sp() - result_count as u32 * 8;
    unsafe {
        for i in 0..result_count as u32 {
            let val = stack.read_u64(results_start + i * 8);
            stack.write_u64(current_locals_sp + i * 8, val);
        }
        stack.set_sp(current_locals_sp + result_count as u32 * 8);
    }

    controls.truncate(current_controls_start);

    call_frames.is_empty()
}

// ---------------------------------------------------------------------------
// Public entry points
// ---------------------------------------------------------------------------

/// Invoke a WASM function by export name.
pub fn invoke(
    module: &Module,
    store: &mut Store,
    func_name: &str,
    args: &[Value],
) -> Result<Vec<Value>, ExecError> {
    let func_idx = module
        .export_func(func_name)
        .ok_or_else(|| ExecError::NotFound(format!("function '{func_name}' not exported")))?;
    call(module, store, func_idx, args)
}

/// Call a WASM function by index.
///
/// Creates a fresh mmap'd stack and runs the interpreter loop.
/// Host function imports are called directly without entering
/// the interpreter.
pub fn call(
    module: &Module,
    store: &mut Store,
    func_idx: u32,
    args: &[Value],
) -> Result<Vec<Value>, ExecError> {
    if module.is_import(func_idx) {
        return if let Some(host_fn) = store.host_funcs.get(func_idx as usize) {
            host_fn(args, &mut store.memory).map_err(|e| ExecError::Trap(format!("trap: {e}")))
        } else {
            Err(ExecError::Trap(format!(
                "unresolved import function {func_idx}"
            )))
        };
    }

    let mut stack = Stack::new();
    super::exec::execute(&mut stack, module, store, func_idx, args)
}
