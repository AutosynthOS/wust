use crate::runtime::module::Module;
use crate::runtime::opcode::*;
use crate::runtime::store::{Store, EXTERN_FUNC_BASE};
use crate::runtime::value::Value;

// TODO: tune once runtime is stable. Catches infinite loops during testing.
const MAX_STEPS: u64 = 1_000_000_000;
const MAX_CALL_DEPTH: usize = 10_000;

#[derive(Debug)]
pub enum ExecError {
    Trap(String),
    NotFound(String),
}

impl std::fmt::Display for ExecError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExecError::Trap(msg) => write!(f, "trap: {msg}"),
            ExecError::NotFound(msg) => write!(f, "not found: {msg}"),
        }
    }
}

struct Frame<'a> {
    pc: usize,
    /// Index into the shared `stack` where this frame's locals begin.
    locals_start: usize,
    /// The stack height when this frame was entered (after locals are allocated).
    stack_height: usize,
    /// Index into the shared `labels` vec where this frame's labels begin.
    labels_start: usize,
    arity: usize,
    body: &'a [Op],
    br_tables: &'a [(Vec<u32>, u32)],
}

struct Label {
    target: usize,
    stack_height: usize,
    arity: usize,
    is_loop: bool,
}

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

fn new_frame<'a>(
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


fn do_return(
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

/// WASM float min with NaN propagation and signed zero handling.
fn wasm_min<F: Float>(a: F, b: F) -> F {
    if a.is_nan() || b.is_nan() {
        F::NAN
    } else if a.is_zero() && b.is_zero() {
        if a.is_sign_negative() || b.is_sign_negative() { F::NEG_ZERO } else { F::ZERO }
    } else {
        a.float_min(b)
    }
}

/// WASM float max with NaN propagation and signed zero handling.
fn wasm_max<F: Float>(a: F, b: F) -> F {
    if a.is_nan() || b.is_nan() {
        F::NAN
    } else if a.is_zero() && b.is_zero() {
        if a.is_sign_positive() || b.is_sign_positive() { F::ZERO } else { F::NEG_ZERO }
    } else {
        a.float_max(b)
    }
}

/// WASM nearest (round ties to even).
fn wasm_nearest<F: Float>(a: F) -> F {
    if a.is_nan() || a.is_infinite() || a.is_zero() {
        return a;
    }
    let trunc = a.float_trunc();
    let frac = a.float_sub(trunc).float_abs();
    if frac.eq_half() {
        // Tie: round to even
        if trunc.is_even() { trunc } else { trunc.float_add(a.float_signum()) }
    } else if frac.gt_half() {
        trunc.float_add(a.float_signum())
    } else {
        trunc
    }
}

trait Float: Copy {
    const NAN: Self;
    const ZERO: Self;
    const NEG_ZERO: Self;
    fn is_nan(self) -> bool;
    fn is_infinite(self) -> bool;
    fn is_zero(self) -> bool;
    fn is_sign_negative(self) -> bool;
    fn is_sign_positive(self) -> bool;
    fn is_even(self) -> bool;
    fn eq_half(self) -> bool;
    fn gt_half(self) -> bool;
    fn float_min(self, other: Self) -> Self;
    fn float_max(self, other: Self) -> Self;
    fn float_trunc(self) -> Self;
    fn float_abs(self) -> Self;
    fn float_sub(self, other: Self) -> Self;
    fn float_add(self, other: Self) -> Self;
    fn float_signum(self) -> Self;
}

impl Float for f32 {
    const NAN: Self = f32::NAN;
    const ZERO: Self = 0.0;
    const NEG_ZERO: Self = -0.0;
    fn is_nan(self) -> bool { self.is_nan() }
    fn is_infinite(self) -> bool { self.is_infinite() }
    fn is_zero(self) -> bool { self == 0.0 }
    fn is_sign_negative(self) -> bool { self.is_sign_negative() }
    fn is_sign_positive(self) -> bool { self.is_sign_positive() }
    fn is_even(self) -> bool { self % 2.0 == 0.0 }
    fn eq_half(self) -> bool { self == 0.5 }
    fn gt_half(self) -> bool { self > 0.5 }
    fn float_min(self, other: Self) -> Self { self.min(other) }
    fn float_max(self, other: Self) -> Self { self.max(other) }
    fn float_trunc(self) -> Self { self.trunc() }
    fn float_abs(self) -> Self { self.abs() }
    fn float_sub(self, other: Self) -> Self { self - other }
    fn float_add(self, other: Self) -> Self { self + other }
    fn float_signum(self) -> Self { self.signum() }
}

impl Float for f64 {
    const NAN: Self = f64::NAN;
    const ZERO: Self = 0.0;
    const NEG_ZERO: Self = -0.0;
    fn is_nan(self) -> bool { self.is_nan() }
    fn is_infinite(self) -> bool { self.is_infinite() }
    fn is_zero(self) -> bool { self == 0.0 }
    fn is_sign_negative(self) -> bool { self.is_sign_negative() }
    fn is_sign_positive(self) -> bool { self.is_sign_positive() }
    fn is_even(self) -> bool { self % 2.0 == 0.0 }
    fn eq_half(self) -> bool { self == 0.5 }
    fn gt_half(self) -> bool { self > 0.5 }
    fn float_min(self, other: Self) -> Self { self.min(other) }
    fn float_max(self, other: Self) -> Self { self.max(other) }
    fn float_trunc(self) -> Self { self.trunc() }
    fn float_abs(self) -> Self { self.abs() }
    fn float_sub(self, other: Self) -> Self { self - other }
    fn float_add(self, other: Self) -> Self { self + other }
    fn float_signum(self) -> Self { self.signum() }
}

// --- Stack helper functions for u64-based stack ---
// WASM validation guarantees stack is non-empty at every pop site.

#[inline(always)]
fn pop_raw(stack: &mut Vec<u64>) -> u64 {
    stack.pop().unwrap()
}

#[inline(always)]
fn pop_i32(stack: &mut Vec<u64>) -> i32 {
    stack.pop().unwrap() as i32
}

#[inline(always)]
fn pop_i64(stack: &mut Vec<u64>) -> i64 {
    stack.pop().unwrap() as i64
}

#[inline(always)]
fn pop_f32(stack: &mut Vec<u64>) -> f32 {
    f32::from_bits(stack.pop().unwrap() as u32)
}

#[inline(always)]
fn pop_f64(stack: &mut Vec<u64>) -> f64 {
    f64::from_bits(stack.pop().unwrap())
}
macro_rules! push_i32 {
    ($stack:expr, $v:expr) => { $stack.push($v as u32 as u64) }
}
macro_rules! push_i64 {
    ($stack:expr, $v:expr) => { $stack.push($v as u64) }
}
macro_rules! push_f32 {
    ($stack:expr, $v:expr) => { $stack.push(($v).to_bits() as u64) }
}
macro_rules! push_f64 {
    ($stack:expr, $v:expr) => { $stack.push(($v).to_bits()) }
}

macro_rules! mem_load {
    ($stack:expr, $store:expr, $offset:expr, $N:literal, $conv:expr) => {{
        let base = pop_i32(&mut $stack) as u32 as u64;
        let bytes = $store
            .memory_load::<$N>(base + $offset)
            .map_err(|e| ExecError::Trap(e.into()))?;
        $stack.push($conv(bytes));
    }};
}

macro_rules! mem_store {
    ($stack:expr, $store:expr, $offset:expr, $pop_fn:ident, $conv:expr) => {{
        let val = $pop_fn(&mut $stack);
        let base = pop_i32(&mut $stack) as u32 as u64;
        $store
            .memory_store(base + $offset, &$conv(val))
            .map_err(|e| ExecError::Trap(e.into()))?;
    }};
}

macro_rules! binop_i32 {
    ($stack:expr, $op:expr) => {{
        let b = pop_i32(&mut $stack);
        let a = pop_i32(&mut $stack);
        push_i32!($stack, $op(a, b));
    }};
}

macro_rules! binop_i64 {
    ($stack:expr, $op:expr) => {{
        let b = pop_i64(&mut $stack);
        let a = pop_i64(&mut $stack);
        push_i64!($stack, $op(a, b));
    }};
}

macro_rules! binop_f32 {
    ($stack:expr, $op:expr) => {{
        let b = pop_f32(&mut $stack);
        let a = pop_f32(&mut $stack);
        push_f32!($stack, $op(a, b));
    }};
}

macro_rules! binop_f64 {
    ($stack:expr, $op:expr) => {{
        let b = pop_f64(&mut $stack);
        let a = pop_f64(&mut $stack);
        push_f64!($stack, $op(a, b));
    }};
}

macro_rules! unop_i32 {
    ($stack:expr, $op:expr) => {{
        let a = pop_i32(&mut $stack);
        push_i32!($stack, $op(a));
    }};
}

macro_rules! unop_i64 {
    ($stack:expr, $op:expr) => {{
        let a = pop_i64(&mut $stack);
        push_i64!($stack, $op(a));
    }};
}

macro_rules! unop_f32 {
    ($stack:expr, $op:expr) => {{
        let a = pop_f32(&mut $stack);
        push_f32!($stack, $op(a));
    }};
}

macro_rules! unop_f64 {
    ($stack:expr, $op:expr) => {{
        let a = pop_f64(&mut $stack);
        push_f64!($stack, $op(a));
    }};
}

macro_rules! cmpop_i32 {
    ($stack:expr, $op:expr) => {{
        let b = pop_i32(&mut $stack);
        let a = pop_i32(&mut $stack);
        push_i32!($stack, if $op(a, b) { 1i32 } else { 0i32 });
    }};
}

macro_rules! cmpop_i64 {
    ($stack:expr, $op:expr) => {{
        let b = pop_i64(&mut $stack);
        let a = pop_i64(&mut $stack);
        push_i32!($stack, if $op(a, b) { 1i32 } else { 0i32 });
    }};
}

macro_rules! cmpop_f32 {
    ($stack:expr, $op:expr) => {{
        let b = pop_f32(&mut $stack);
        let a = pop_f32(&mut $stack);
        push_i32!($stack, if $op(a, b) { 1i32 } else { 0i32 });
    }};
}

macro_rules! cmpop_f64 {
    ($stack:expr, $op:expr) => {{
        let b = pop_f64(&mut $stack);
        let a = pop_f64(&mut $stack);
        push_i32!($stack, if $op(a, b) { 1i32 } else { 0i32 });
    }};
}

macro_rules! trunc_op {
    ($stack:expr, $pop_fn:ident, $push_macro:ident, $int_ty:ty, $max_bound:expr, $min_bound:expr) => {{
        let a = $pop_fn(&mut $stack);
        if a.is_nan() {
            return Err(ExecError::Trap("invalid conversion to integer".into()));
        }
        if a.is_infinite() {
            return Err(ExecError::Trap("integer overflow".into()));
        }
        let t = a.trunc();
        if t >= $max_bound || t < $min_bound {
            return Err(ExecError::Trap("integer overflow".into()));
        }
        $push_macro!($stack, t as $int_ty);
    }};
}

macro_rules! trunc_op_u {
    ($stack:expr, $pop_fn:ident, $push_macro:ident, $uint_ty:ty, $int_ty:ty, $max_bound:expr) => {{
        let a = $pop_fn(&mut $stack);
        if a.is_nan() {
            return Err(ExecError::Trap("invalid conversion to integer".into()));
        }
        if a.is_infinite() {
            return Err(ExecError::Trap("integer overflow".into()));
        }
        let t = a.trunc();
        if t >= $max_bound || t < 0.0 {
            return Err(ExecError::Trap("integer overflow".into()));
        }
        $push_macro!($stack, t as $uint_ty as $int_ty);
    }};
}

/// Convert raw bits to a Value matching the type of an existing global.
fn coerce_bits_to_global(bits: u64, existing: &Value) -> Result<Value, ExecError> {
    match existing {
        Value::I32(_) => Ok(Value::I32(bits as i32)),
        Value::I64(_) => Ok(Value::I64(bits as i64)),
        Value::F32(_) => Ok(Value::F32(f32::from_bits(bits as u32))),
        Value::F64(_) => Ok(Value::F64(f64::from_bits(bits))),
        Value::FuncRef(_) => {
            if bits == u64::MAX { Ok(Value::FuncRef(None)) }
            else { Ok(Value::FuncRef(Some(bits as u32))) }
        }
        Value::V128(_) => Err(ExecError::Trap("v128 globals not supported".into())),
    }
}

/// Convert a raw u64 on the stack to a Value based on its ValType.
#[inline(always)]
fn bits_to_value(bits: u64, ty: wasmparser::ValType) -> Value {
    match ty {
        wasmparser::ValType::I32 => Value::I32(bits as i32),
        wasmparser::ValType::I64 => Value::I64(bits as i64),
        wasmparser::ValType::F32 => Value::F32(f32::from_bits(bits as u32)),
        wasmparser::ValType::F64 => Value::F64(f64::from_bits(bits)),
        wasmparser::ValType::Ref(_) => {
            if bits == u64::MAX { Value::FuncRef(None) }
            else { Value::FuncRef(Some(bits as u32)) }
        }
        _ => Value::I32(0),
    }
}

/// Pop N args from the stack, convert to Values based on param types.
fn pop_args_as_values(stack: &mut Vec<u64>, param_types: &[wasmparser::ValType]) -> Vec<Value> {
    let param_count = param_types.len();
    let args: Vec<Value> = param_types.iter().enumerate().map(|(i, &ty)| {
        bits_to_value(stack[stack.len() - param_count + i], ty)
    }).collect();
    stack.truncate(stack.len() - param_count);
    args
}

/// Call a host function: pop args, invoke, push results.
fn call_host_fn(
    stack: &mut Vec<u64>,
    host_fn: &dyn Fn(&[Value], &mut [u8]) -> Result<Vec<Value>, String>,
    param_types: &[wasmparser::ValType],
    memory: &mut [u8],
) -> Result<(), ExecError> {
    let args = pop_args_as_values(stack, param_types);
    let results = host_fn(&args, memory)
        .map_err(|e| ExecError::Trap(format!("trap: {e}")))?;
    for r in results {
        stack.push(r.to_bits());
    }
    Ok(())
}

/// Set up a local (non-import) call: extend stack with zero locals, push label, swap frame.
fn setup_local_call<'a>(
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

/// Copy elements from an element segment into a table, with bounds checking.
fn execute_table_init(
    store: &mut Store,
    elem_idx: usize,
    table_idx: usize,
    dst: u32,
    src: u32,
    count: u32,
) -> Result<(), ExecError> {
    let seg = store.elem_segments.get(elem_idx)
        .ok_or_else(|| ExecError::Trap("unknown elem segment".into()))?;
    // Clone the relevant slice to avoid holding an immutable borrow on
    // elem_segments while we mutably borrow tables below.
    let elems = match seg {
        None => {
            if count > 0 {
                return Err(ExecError::Trap("out of bounds table access".into()));
            }
            return Ok(());
        }
        Some(elems) => {
            if src as usize + count as usize > elems.len() {
                return Err(ExecError::Trap("out of bounds table access".into()));
            }
            elems[src as usize..src as usize + count as usize].to_vec()
        }
    };
    let shared_table = store.tables.get(table_idx)
        .ok_or_else(|| ExecError::Trap("undefined table".into()))?;
    let mut table = shared_table.borrow_mut();
    if dst as usize + count as usize > table.len() {
        return Err(ExecError::Trap("out of bounds table access".into()));
    }
    for (i, elem) in elems.iter().enumerate() {
        table[dst as usize + i] = *elem;
    }
    Ok(())
}

/// Copy bytes from a data segment into memory, with bounds checking.
fn execute_memory_init(
    store: &mut Store,
    seg_idx: usize,
    dst: u32,
    src: u32,
    count: u32,
) -> Result<(), ExecError> {
    let seg = store.data_segments.get(seg_idx)
        .ok_or_else(|| ExecError::Trap("unknown data segment".into()))?;
    match seg {
        None => {
            if count > 0 || src > 0 {
                return Err(ExecError::Trap("out of bounds memory access".into()));
            }
        }
        Some(data) => {
            if src as u64 + count as u64 > data.len() as u64 {
                return Err(ExecError::Trap("out of bounds memory access".into()));
            }
            if dst as u64 + count as u64 > store.memory.len() as u64 {
                return Err(ExecError::Trap("out of bounds memory access".into()));
            }
            let src_copy = data[src as usize..(src + count) as usize].to_vec();
            store.memory[dst as usize..(dst + count) as usize]
                .copy_from_slice(&src_copy);
        }
    }
    Ok(())
}

/// Copy elements between tables (or within the same table), with bounds checking.
fn execute_table_copy(
    store: &mut Store,
    dst_table: usize,
    src_table: usize,
    dst: u32,
    src: u32,
    count: u32,
) -> Result<(), ExecError> {
    let src_len = store.tables.get(src_table)
        .ok_or_else(|| ExecError::Trap("undefined table".into()))?.borrow().len();
    let dst_len = store.tables.get(dst_table)
        .ok_or_else(|| ExecError::Trap("undefined table".into()))?.borrow().len();
    if src as u64 + count as u64 > src_len as u64
        || dst as u64 + count as u64 > dst_len as u64
    {
        return Err(ExecError::Trap("out of bounds table access".into()));
    }
    if count > 0 {
        if src_table == dst_table {
            let mut table = store.tables[src_table].borrow_mut();
            table.copy_within(src as usize..(src + count) as usize, dst as usize);
        } else {
            let tmp: Vec<_> = {
                let src_t = store.tables[src_table].borrow();
                (0..count as usize)
                    .map(|i| src_t[src as usize + i])
                    .collect()
            };
            let mut dst_t = store.tables[dst_table].borrow_mut();
            for (i, val) in tmp.into_iter().enumerate() {
                dst_t[dst as usize + i] = val;
            }
        }
    }
    Ok(())
}

/// Look up a function index from a table element, returning an error if out of bounds or null.
fn resolve_table_element(store: &Store, table_idx: u32, elem_idx: u32) -> Result<u32, ExecError> {
    let shared_table = store.tables.get(table_idx as usize)
        .ok_or_else(|| ExecError::Trap("undefined table".into()))?;
    let table = shared_table.borrow();
    let entry = table.get(elem_idx as usize)
        .ok_or_else(|| ExecError::Trap("undefined element".into()))?;
    entry.ok_or_else(|| ExecError::Trap("uninitialized element".into()))
}

/// Validate that a callee's type matches the expected indirect call type.
fn check_indirect_type(
    module: &Module,
    func_idx: u32,
    expected: &wasmparser::FuncType,
) -> Result<(), ExecError> {
    let callee_type_idx = *module.func_types.get(func_idx as usize)
        .ok_or_else(|| ExecError::Trap(format!("func type index {} out of bounds", func_idx)))?;
    let callee_type = module.types.get(callee_type_idx as usize)
        .ok_or_else(|| ExecError::Trap(format!("type index {} out of bounds", callee_type_idx)))?;
    if *callee_type != *expected {
        return Err(ExecError::Trap("indirect call type mismatch".into()));
    }
    Ok(())
}

/// Convert raw u64 stack values to Value types for the public API, using the function's result types.
fn raw_to_values(raw: &[u64], types: &[wasmparser::ValType]) -> Vec<Value> {
    raw.iter().zip(types.iter()).map(|(&bits, &ty)| {
        bits_to_value(bits, ty)
    }).collect()
}

pub fn call(
    module: &Module,
    store: &mut Store,
    func_idx: u32,
    args: &[Value],
) -> Result<Vec<Value>, ExecError> {
    // If the target is an imported host function, call it directly
    if module.is_import(func_idx) {
        return if let Some(host_fn) = store.host_funcs.get(func_idx as usize) {
            host_fn(args, &mut store.memory)
                .map_err(|e| ExecError::Trap(format!("trap: {e}")))
        } else {
            Err(ExecError::Trap(format!("unresolved import function {func_idx}")))
        };
    }

    let mut stack: Vec<u64> = Vec::with_capacity(256);
    let mut call_stack: Vec<Frame<'_>> = Vec::with_capacity(64);
    let mut labels: Vec<Label> = Vec::with_capacity(64);
    let top_func = module.get_func(func_idx)
        .ok_or_else(|| ExecError::NotFound(format!("function {func_idx} not found")))?;
    let mut frame = new_frame(module, func_idx, args, &mut stack, &mut labels)?;

    // Get result types for the top-level function to convert raw results back
    let top_func_type = module.types.get(top_func.type_idx as usize)
        .ok_or_else(|| ExecError::Trap(format!("type index {} out of bounds", top_func.type_idx)))?;
    let result_types: Vec<wasmparser::ValType> = top_func_type.results().to_vec();

    let mut steps = 0u64;
    loop {
        // TODO: remove per-instruction step counting once runtime is stable.
        // Currently needed to catch infinite loops in tight code (e.g. boa's
        // tokenizer/parser) that never call imported functions.
        steps += 1;
        if steps > MAX_STEPS {
            return Err(ExecError::Trap("execution limit".into()));
        }

        if frame.pc >= frame.body.len() {
            if do_return(&frame, &mut stack, &mut labels, &mut call_stack) {
                let raw_results: Vec<u64> = stack.drain(stack.len() - result_types.len()..).collect();
                return Ok(raw_to_values(&raw_results, &result_types));
            }
            frame = call_stack.pop().unwrap();
            continue;
        }

        let op = frame.body[frame.pc];
        frame.pc += 1;

        match op.code {
            OP_UNREACHABLE => {
                return Err(ExecError::Trap("unreachable".into()));
            }
            OP_NOP => {}

            // --- Control flow ---
            OP_BLOCK => {
                let end_pc = op.imm_hi() as usize;
                let arity = op.imm_lo() as usize;
                labels.push(Label {
                    target: end_pc,
                    stack_height: stack.len(),
                    arity,
                    is_loop: false,
                });
            }
            OP_LOOP => {
                let arity = op.imm_u32() as usize;
                labels.push(Label {
                    target: frame.pc - 1,
                    stack_height: stack.len(),
                    arity,
                    is_loop: true,
                });
            }
            OP_IF => {
                // No else branch: imm = (end_pc << 32) | arity
                let cond = pop_i32(&mut stack);
                let end_pc = op.imm_hi() as usize;
                let arity = op.imm_lo() as usize;
                labels.push(Label {
                    target: end_pc,
                    stack_height: stack.len(),
                    arity,
                    is_loop: false,
                });
                if cond == 0 {
                    frame.pc = end_pc + 1;
                    labels.pop();
                }
            }
            OP_IF_ELSE => {
                // imm = (arity << 56) | (end_pc << 28) | else_pc
                let cond = pop_i32(&mut stack);
                let arity = (op.imm >> 56) as usize;
                let end_pc = ((op.imm >> 28) & 0x0FFF_FFFF) as usize;
                let else_pc = (op.imm & 0x0FFF_FFFF) as usize;
                labels.push(Label {
                    target: end_pc,
                    stack_height: stack.len(),
                    arity,
                    is_loop: false,
                });
                if cond == 0 {
                    frame.pc = else_pc + 1;
                }
            }
            OP_ELSE => {
                let label = labels.last().unwrap();
                frame.pc = label.target + 1;
                labels.pop();
            }
            OP_END => {
                if labels.len() > frame.labels_start + 1 {
                    labels.pop();
                }
            }
            OP_BR => {
                do_br(&mut frame, &mut stack, &mut labels, op.imm_u32(), &mut steps)?;
            }
            OP_BR_IF => {
                let cond = pop_i32(&mut stack);
                if cond != 0 {
                    do_br(&mut frame, &mut stack, &mut labels, op.imm_u32(), &mut steps)?;
                }
            }
            OP_BR_TABLE => {
                let (ref targets, default) = frame.br_tables[op.imm as usize];
                let idx = pop_i32(&mut stack) as usize;
                let depth = if idx < targets.len() { targets[idx] } else { default };
                do_br(&mut frame, &mut stack, &mut labels, depth, &mut steps)?;
            }
            OP_RETURN => {
                if do_return(&frame, &mut stack, &mut labels, &mut call_stack) {
                    let raw_results: Vec<u64> = stack.drain(stack.len() - result_types.len()..).collect();
                    return Ok(raw_to_values(&raw_results, &result_types));
                }
                frame = call_stack.pop().unwrap();
                continue;
            }
            OP_CALL => {
                let idx = op.imm_u32();
                steps += 1;
                if steps > MAX_STEPS {
                    return Err(ExecError::Trap("execution limit".into()));
                }
                if module.is_import(idx) {
                    let type_idx = *module.func_types.get(idx as usize)
                        .ok_or_else(|| ExecError::Trap(format!("func type index {} out of bounds", idx)))?;
                    let callee_type = module.types.get(type_idx as usize)
                        .ok_or_else(|| ExecError::Trap(format!("type index {} out of bounds", type_idx)))?;
                    let host_fn = store.host_funcs.get(idx as usize)
                        .ok_or_else(|| ExecError::Trap(format!("unresolved import function {idx}")))?;
                    call_host_fn(&mut stack, host_fn.as_ref(), callee_type.params(), &mut store.memory)?;
                } else {
                    let callee = module.get_func(idx)
                        .ok_or_else(|| ExecError::Trap(format!("function {idx} not found")))?;
                    let callee_type = module.types.get(callee.type_idx as usize)
                        .ok_or_else(|| ExecError::Trap(format!("type index {} out of bounds", callee.type_idx)))?;
                    setup_local_call(&mut frame, &mut call_stack, &mut stack, &mut labels, callee, callee_type)?;
                }
            }
            OP_CALL_INDIRECT => {
                let ci_type_idx = op.imm_hi();
                let elem_idx = pop_i32(&mut stack) as u32;
                let func_idx = resolve_table_element(store, op.imm_lo(), elem_idx)?;
                let ci_type = module.types.get(ci_type_idx as usize)
                    .ok_or_else(|| ExecError::Trap(format!("type index {} out of bounds", ci_type_idx)))?;

                if func_idx >= EXTERN_FUNC_BASE {
                    let extern_idx = (func_idx - EXTERN_FUNC_BASE) as usize;
                    let extern_fn = store.extern_funcs.get(extern_idx)
                        .ok_or_else(|| ExecError::Trap(format!("unresolved extern function {func_idx}")))?;
                    call_host_fn(&mut stack, extern_fn.as_ref(), ci_type.params(), &mut store.memory)?;
                } else if module.is_import(func_idx) {
                    check_indirect_type(module, func_idx, ci_type)?;
                    let host_fn = store.host_funcs.get(func_idx as usize)
                        .ok_or_else(|| ExecError::Trap(format!("unresolved import function {func_idx}")))?;
                    call_host_fn(&mut stack, host_fn.as_ref(), ci_type.params(), &mut store.memory)?;
                } else {
                    let callee = module.get_func(func_idx)
                        .ok_or_else(|| ExecError::Trap(format!("function {func_idx} not found")))?;
                    let callee_type = module.types.get(callee.type_idx as usize)
                        .ok_or_else(|| ExecError::Trap(format!("type index {} out of bounds", callee.type_idx)))?;
                    if *callee_type != *ci_type {
                        return Err(ExecError::Trap("indirect call type mismatch".into()));
                    }
                    setup_local_call(&mut frame, &mut call_stack, &mut stack, &mut labels, callee, callee_type)?;
                }
            }

            OP_DROP => { pop_raw(&mut stack); }
            OP_SELECT => {
                let cond = pop_i32(&mut stack);
                let b = pop_raw(&mut stack);
                let a = pop_raw(&mut stack);
                stack.push(if cond != 0 { a } else { b });
            }

            // --- Superinstructions ---
            OP_LOCAL_GET_I32_CONST => {
                let idx = op.imm_hi() as usize;
                let val = op.imm_lo();
                stack.push(stack[frame.locals_start + idx]);
                stack.push(val as u64);
            }
            OP_LOCAL_GET_LOCAL_GET => {
                let a = op.imm_hi() as usize;
                let b = op.imm_lo() as usize;
                let va = stack[frame.locals_start + a];
                let vb = stack[frame.locals_start + b];
                stack.push(va);
                stack.push(vb);
            }

            // --- Locals / Globals ---
            OP_LOCAL_GET => {
                let v = stack[frame.locals_start + op.imm as usize];
                stack.push(v);
            }
            OP_LOCAL_SET => {
                let v = pop_raw(&mut stack);
                stack[frame.locals_start + op.imm as usize] = v;
            }
            OP_LOCAL_TEE => {
                let v = *stack.last().unwrap();
                stack[frame.locals_start + op.imm as usize] = v;
            }
            OP_GLOBAL_GET => {
                let g = store.globals.get(op.imm as usize)
                    .ok_or_else(|| ExecError::Trap(format!("global index {} out of bounds", op.imm)))?;
                stack.push(g.to_bits());
            }
            OP_GLOBAL_SET => {
                let bits = pop_raw(&mut stack);
                let idx = op.imm as usize;
                let g = store.globals.get(idx)
                    .ok_or_else(|| ExecError::Trap(format!("global index {} out of bounds", idx)))?;
                store.globals[idx] = coerce_bits_to_global(bits, g)?;
            }

            // --- Memory loads ---
            OP_I32_LOAD => mem_load!(stack, store, &op.imm, 4, |b: [u8;4]| i32::from_le_bytes(b) as u32 as u64),
            OP_I64_LOAD => mem_load!(stack, store, &op.imm, 8, |b: [u8;8]| i64::from_le_bytes(b) as u64),
            OP_F32_LOAD => mem_load!(stack, store, &op.imm, 4, |b: [u8;4]| u32::from_le_bytes(b) as u64),
            OP_F64_LOAD => mem_load!(stack, store, &op.imm, 8, |b: [u8;8]| u64::from_le_bytes(b)),
            OP_I32_LOAD8_S => mem_load!(stack, store, &op.imm, 1, |b: [u8;1]| (b[0] as i8 as i32) as u32 as u64),
            OP_I32_LOAD8_U => mem_load!(stack, store, &op.imm, 1, |b: [u8;1]| b[0] as u64),
            OP_I32_LOAD16_S => mem_load!(stack, store, &op.imm, 2, |b: [u8;2]| (i16::from_le_bytes(b) as i32) as u32 as u64),
            OP_I32_LOAD16_U => mem_load!(stack, store, &op.imm, 2, |b: [u8;2]| u16::from_le_bytes(b) as u64),
            OP_I64_LOAD8_S => mem_load!(stack, store, &op.imm, 1, |b: [u8;1]| (b[0] as i8 as i64) as u64),
            OP_I64_LOAD8_U => mem_load!(stack, store, &op.imm, 1, |b: [u8;1]| b[0] as u64),
            OP_I64_LOAD16_S => mem_load!(stack, store, &op.imm, 2, |b: [u8;2]| (i16::from_le_bytes(b) as i64) as u64),
            OP_I64_LOAD16_U => mem_load!(stack, store, &op.imm, 2, |b: [u8;2]| u16::from_le_bytes(b) as u64),
            OP_I64_LOAD32_S => mem_load!(stack, store, &op.imm, 4, |b: [u8;4]| (i32::from_le_bytes(b) as i64) as u64),
            OP_I64_LOAD32_U => mem_load!(stack, store, &op.imm, 4, |b: [u8;4]| u32::from_le_bytes(b) as u64),

            // --- Memory stores ---
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
                let pages = pop_i32(&mut stack);
                push_i32!(stack, store.memory_grow(pages as u32));
            }

            // --- Constants ---
            OP_I32_CONST => stack.push(op.imm),
            OP_I64_CONST => stack.push(op.imm),
            OP_F32_CONST => stack.push(op.imm),
            OP_F64_CONST => stack.push(op.imm),

            // --- i32 comparison ---
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

            // --- i32 arithmetic ---
            OP_I32_CLZ => unop_i32!(stack, |a: i32| a.leading_zeros() as i32),
            OP_I32_CTZ => unop_i32!(stack, |a: i32| a.trailing_zeros() as i32),
            OP_I32_POPCNT => unop_i32!(stack, |a: i32| a.count_ones() as i32),
            OP_I32_ADD => binop_i32!(stack, |a: i32, b: i32| a.wrapping_add(b)),
            OP_I32_SUB => binop_i32!(stack, |a: i32, b: i32| a.wrapping_sub(b)),
            OP_I32_MUL => binop_i32!(stack, |a: i32, b: i32| a.wrapping_mul(b)),
            OP_I32_DIV_S => {
                let b = pop_i32(&mut stack);
                let a = pop_i32(&mut stack);
                if b == 0 { return Err(ExecError::Trap("integer divide by zero".into())); }
                if a == i32::MIN && b == -1 { return Err(ExecError::Trap("integer overflow".into())); }
                push_i32!(stack, a.wrapping_div(b));
            }
            OP_I32_DIV_U => {
                let b = pop_i32(&mut stack) as u32;
                let a = pop_i32(&mut stack) as u32;
                if b == 0 { return Err(ExecError::Trap("integer divide by zero".into())); }
                push_i32!(stack, (a / b) as i32);
            }
            OP_I32_REM_S => {
                let b = pop_i32(&mut stack);
                let a = pop_i32(&mut stack);
                if b == 0 { return Err(ExecError::Trap("integer divide by zero".into())); }
                push_i32!(stack, if a == i32::MIN && b == -1 { 0 } else { a.wrapping_rem(b) });
            }
            OP_I32_REM_U => {
                let b = pop_i32(&mut stack) as u32;
                let a = pop_i32(&mut stack) as u32;
                if b == 0 { return Err(ExecError::Trap("integer divide by zero".into())); }
                push_i32!(stack, (a % b) as i32);
            }
            OP_I32_AND => binop_i32!(stack, |a: i32, b: i32| a & b),
            OP_I32_OR => binop_i32!(stack, |a: i32, b: i32| a | b),
            OP_I32_XOR => binop_i32!(stack, |a: i32, b: i32| a ^ b),
            OP_I32_SHL => binop_i32!(stack, |a: i32, b: i32| a.wrapping_shl(b as u32)),
            OP_I32_SHR_S => binop_i32!(stack, |a: i32, b: i32| a.wrapping_shr(b as u32)),
            OP_I32_SHR_U => {
                let b = pop_i32(&mut stack) as u32;
                let a = pop_i32(&mut stack) as u32;
                push_i32!(stack, a.wrapping_shr(b) as i32);
            }
            OP_I32_ROTL => binop_i32!(stack, |a: i32, b: i32| a.rotate_left(b as u32)),
            OP_I32_ROTR => binop_i32!(stack, |a: i32, b: i32| a.rotate_right(b as u32)),

            // --- i64 comparison ---
            OP_I64_EQZ => {
                let a = pop_i64(&mut stack);
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

            // --- i64 arithmetic ---
            OP_I64_CLZ => unop_i64!(stack, |a: i64| a.leading_zeros() as i64),
            OP_I64_CTZ => unop_i64!(stack, |a: i64| a.trailing_zeros() as i64),
            OP_I64_POPCNT => unop_i64!(stack, |a: i64| a.count_ones() as i64),
            OP_I64_ADD => binop_i64!(stack, |a: i64, b: i64| a.wrapping_add(b)),
            OP_I64_SUB => binop_i64!(stack, |a: i64, b: i64| a.wrapping_sub(b)),
            OP_I64_MUL => binop_i64!(stack, |a: i64, b: i64| a.wrapping_mul(b)),
            OP_I64_DIV_S => {
                let b = pop_i64(&mut stack);
                let a = pop_i64(&mut stack);
                if b == 0 { return Err(ExecError::Trap("integer divide by zero".into())); }
                if a == i64::MIN && b == -1 { return Err(ExecError::Trap("integer overflow".into())); }
                push_i64!(stack, a.wrapping_div(b));
            }
            OP_I64_DIV_U => {
                let b = pop_i64(&mut stack) as u64;
                let a = pop_i64(&mut stack) as u64;
                if b == 0 { return Err(ExecError::Trap("integer divide by zero".into())); }
                push_i64!(stack, (a / b) as i64);
            }
            OP_I64_REM_S => {
                let b = pop_i64(&mut stack);
                let a = pop_i64(&mut stack);
                if b == 0 { return Err(ExecError::Trap("integer divide by zero".into())); }
                push_i64!(stack, if a == i64::MIN && b == -1 { 0 } else { a.wrapping_rem(b) });
            }
            OP_I64_REM_U => {
                let b = pop_i64(&mut stack) as u64;
                let a = pop_i64(&mut stack) as u64;
                if b == 0 { return Err(ExecError::Trap("integer divide by zero".into())); }
                push_i64!(stack, (a % b) as i64);
            }
            OP_I64_AND => binop_i64!(stack, |a: i64, b: i64| a & b),
            OP_I64_OR => binop_i64!(stack, |a: i64, b: i64| a | b),
            OP_I64_XOR => binop_i64!(stack, |a: i64, b: i64| a ^ b),
            OP_I64_SHL => binop_i64!(stack, |a: i64, b: i64| a.wrapping_shl(b as u32)),
            OP_I64_SHR_S => binop_i64!(stack, |a: i64, b: i64| a.wrapping_shr(b as u32)),
            OP_I64_SHR_U => {
                let b = pop_i64(&mut stack) as u64;
                let a = pop_i64(&mut stack) as u64;
                push_i64!(stack, a.wrapping_shr(b as u32) as i64);
            }
            OP_I64_ROTL => binop_i64!(stack, |a: i64, b: i64| a.rotate_left(b as u32)),
            OP_I64_ROTR => binop_i64!(stack, |a: i64, b: i64| a.rotate_right(b as u32)),

            // --- Conversions ---
            OP_I32_WRAP_I64 => {
                let a = pop_i64(&mut stack);
                push_i32!(stack, a as i32);
            }
            OP_I64_EXTEND_I32_S => {
                let a = pop_i32(&mut stack);
                push_i64!(stack, a as i64);
            }
            OP_I64_EXTEND_I32_U => {
                let a = pop_i32(&mut stack);
                push_i64!(stack, (a as u32) as i64);
            }

            // Sign extension
            OP_I32_EXTEND8_S => unop_i32!(stack, |a: i32| a as i8 as i32),
            OP_I32_EXTEND16_S => unop_i32!(stack, |a: i32| a as i16 as i32),
            OP_I64_EXTEND8_S => unop_i64!(stack, |a: i64| a as i8 as i64),
            OP_I64_EXTEND16_S => unop_i64!(stack, |a: i64| a as i16 as i64),
            OP_I64_EXTEND32_S => unop_i64!(stack, |a: i64| a as i32 as i64),

            // Reinterpret
            OP_I32_REINTERPRET_F32 => {
                let a = pop_f32(&mut stack);
                push_i32!(stack, a.to_bits() as i32);
            }
            OP_I64_REINTERPRET_F64 => {
                let a = pop_f64(&mut stack);
                push_i64!(stack, a.to_bits() as i64);
            }
            OP_F32_REINTERPRET_I32 => {
                let a = pop_i32(&mut stack);
                push_f32!(stack, f32::from_bits(a as u32));
            }
            OP_F64_REINTERPRET_I64 => {
                let a = pop_i64(&mut stack);
                push_f64!(stack, f64::from_bits(a as u64));
            }

            // --- f32 comparison ---
            OP_F32_EQ => cmpop_f32!(stack, |a: f32, b: f32| a == b),
            OP_F32_NE => cmpop_f32!(stack, |a: f32, b: f32| a != b),
            OP_F32_LT => cmpop_f32!(stack, |a: f32, b: f32| a < b),
            OP_F32_GT => cmpop_f32!(stack, |a: f32, b: f32| a > b),
            OP_F32_LE => cmpop_f32!(stack, |a: f32, b: f32| a <= b),
            OP_F32_GE => cmpop_f32!(stack, |a: f32, b: f32| a >= b),

            // --- f64 comparison ---
            OP_F64_EQ => cmpop_f64!(stack, |a: f64, b: f64| a == b),
            OP_F64_NE => cmpop_f64!(stack, |a: f64, b: f64| a != b),
            OP_F64_LT => cmpop_f64!(stack, |a: f64, b: f64| a < b),
            OP_F64_GT => cmpop_f64!(stack, |a: f64, b: f64| a > b),
            OP_F64_LE => cmpop_f64!(stack, |a: f64, b: f64| a <= b),
            OP_F64_GE => cmpop_f64!(stack, |a: f64, b: f64| a >= b),

            // --- f32 arithmetic ---
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

            // --- f64 arithmetic ---
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

            // --- Float-int conversions ---
            OP_I32_TRUNC_F32_S => trunc_op!(stack, pop_f32, push_i32, i32, 2147483648.0_f32, -2147483648.0_f32),
            OP_I32_TRUNC_F32_U => trunc_op_u!(stack, pop_f32, push_i32, u32, i32, 4294967296.0_f32),
            OP_I32_TRUNC_F64_S => trunc_op!(stack, pop_f64, push_i32, i32, 2147483648.0_f64, -2147483648.0_f64),
            OP_I32_TRUNC_F64_U => trunc_op_u!(stack, pop_f64, push_i32, u32, i32, 4294967296.0_f64),
            OP_I64_TRUNC_F32_S => trunc_op!(stack, pop_f32, push_i64, i64, 9223372036854775808.0_f32, -9223372036854775808.0_f32),
            OP_I64_TRUNC_F32_U => trunc_op_u!(stack, pop_f32, push_i64, u64, i64, 18446744073709551616.0_f32),
            OP_I64_TRUNC_F64_S => trunc_op!(stack, pop_f64, push_i64, i64, 9223372036854775808.0_f64, -9223372036854775808.0_f64),
            OP_I64_TRUNC_F64_U => trunc_op_u!(stack, pop_f64, push_i64, u64, i64, 18446744073709551616.0_f64),

            // --- Saturating truncation ---
            OP_I32_TRUNC_SAT_F32_S => {
                let a = pop_f32(&mut stack);
                push_i32!(stack, if a.is_nan() { 0i32 }
                    else if a >= 2147483648.0_f32 { i32::MAX }
                    else if a < -2147483648.0_f32 { i32::MIN }
                    else { a as i32 });
            }
            OP_I32_TRUNC_SAT_F32_U => {
                let a = pop_f32(&mut stack);
                push_i32!(stack, if a.is_nan() || a <= -1.0 { 0u32 as i32 }
                    else if a >= 4294967296.0_f32 { u32::MAX as i32 }
                    else { a as u32 as i32 });
            }
            OP_I32_TRUNC_SAT_F64_S => {
                let a = pop_f64(&mut stack);
                push_i32!(stack, if a.is_nan() { 0i32 }
                    else if a >= 2147483648.0_f64 { i32::MAX }
                    else if a <= -2147483649.0_f64 { i32::MIN }
                    else { a as i32 });
            }
            OP_I32_TRUNC_SAT_F64_U => {
                let a = pop_f64(&mut stack);
                push_i32!(stack, if a.is_nan() || a <= -1.0 { 0u32 as i32 }
                    else if a >= 4294967296.0_f64 { u32::MAX as i32 }
                    else { a as u32 as i32 });
            }
            OP_I64_TRUNC_SAT_F32_S => {
                let a = pop_f32(&mut stack);
                push_i64!(stack, if a.is_nan() { 0i64 }
                    else if a >= 9223372036854775808.0_f32 { i64::MAX }
                    else if a < -9223372036854775808.0_f32 { i64::MIN }
                    else { a as i64 });
            }
            OP_I64_TRUNC_SAT_F32_U => {
                let a = pop_f32(&mut stack);
                push_i64!(stack, if a.is_nan() || a <= -1.0 { 0u64 as i64 }
                    else if a >= 18446744073709551616.0_f32 { u64::MAX as i64 }
                    else { a as u64 as i64 });
            }
            OP_I64_TRUNC_SAT_F64_S => {
                let a = pop_f64(&mut stack);
                push_i64!(stack, if a.is_nan() { 0i64 }
                    else if a >= 9223372036854775808.0_f64 { i64::MAX }
                    else if a < -9223372036854775808.0_f64 { i64::MIN }
                    else { a as i64 });
            }
            OP_I64_TRUNC_SAT_F64_U => {
                let a = pop_f64(&mut stack);
                push_i64!(stack, if a.is_nan() || a <= -1.0 { 0u64 as i64 }
                    else if a >= 18446744073709551616.0_f64 { u64::MAX as i64 }
                    else { a as u64 as i64 });
            }

            OP_F32_CONVERT_I32_S => { let a = pop_i32(&mut stack); push_f32!(stack, a as f32); }
            OP_F32_CONVERT_I32_U => { let a = pop_i32(&mut stack); push_f32!(stack, (a as u32) as f32); }
            OP_F32_CONVERT_I64_S => { let a = pop_i64(&mut stack); push_f32!(stack, a as f32); }
            OP_F32_CONVERT_I64_U => { let a = pop_i64(&mut stack); push_f32!(stack, (a as u64) as f32); }
            OP_F32_DEMOTE_F64 => { let a = pop_f64(&mut stack); push_f32!(stack, a as f32); }
            OP_F64_CONVERT_I32_S => { let a = pop_i32(&mut stack); push_f64!(stack, a as f64); }
            OP_F64_CONVERT_I32_U => { let a = pop_i32(&mut stack); push_f64!(stack, (a as u32) as f64); }
            OP_F64_CONVERT_I64_S => { let a = pop_i64(&mut stack); push_f64!(stack, a as f64); }
            OP_F64_CONVERT_I64_U => { let a = pop_i64(&mut stack); push_f64!(stack, (a as u64) as f64); }
            OP_F64_PROMOTE_F32 => { let a = pop_f32(&mut stack); push_f64!(stack, a as f64); }

            OP_TABLE_INIT => {
                let n = pop_i32(&mut stack) as u32;
                let s = pop_i32(&mut stack) as u32;
                let d = pop_i32(&mut stack) as u32;
                execute_table_init(store, op.imm_hi() as usize, op.imm_lo() as usize, d, s, n)?;
            }
            OP_ELEM_DROP => {
                let elem_idx = op.imm as usize;
                if elem_idx < store.elem_segments.len() {
                    store.elem_segments[elem_idx] = None;
                }
            }

            OP_REF_FUNC => {
                let func_idx = op.imm_u32();
                // Push funcref as u64 (matching Value::FuncRef(Some(idx)).to_bits())
                stack.push(func_idx as u64);
            }
            OP_REF_NULL => {
                // Push null funcref (u64::MAX matches Value::FuncRef(None).to_bits())
                stack.push(u64::MAX);
            }
            OP_REF_IS_NULL => {
                let val = pop_raw(&mut stack);
                // A null funcref is encoded as u64::MAX
                push_i32!(stack, if val == u64::MAX { 1i32 } else { 0i32 });
            }

            OP_MEMORY_INIT => {
                let n = pop_i32(&mut stack) as u32;
                let s = pop_i32(&mut stack) as u32;
                let d = pop_i32(&mut stack) as u32;
                execute_memory_init(store, op.imm as usize, d, s, n)?;
            }
            OP_DATA_DROP => {
                let seg_idx = op.imm as usize;
                if seg_idx < store.data_segments.len() {
                    store.data_segments[seg_idx] = None;
                }
            }
            OP_MEMORY_COPY => {
                let n = pop_i32(&mut stack) as u32;
                let s = pop_i32(&mut stack) as u32;
                let d = pop_i32(&mut stack) as u32;
                if s as u64 + n as u64 > store.memory.len() as u64
                    || d as u64 + n as u64 > store.memory.len() as u64
                {
                    return Err(ExecError::Trap("out of bounds memory access".into()));
                }
                // memmove semantics: handle overlapping regions
                store.memory.copy_within(s as usize..(s + n) as usize, d as usize);
            }
            OP_MEMORY_FILL => {
                let n = pop_i32(&mut stack) as u32;
                let val = pop_i32(&mut stack) as u8;
                let d = pop_i32(&mut stack) as u32;
                if d as u64 + n as u64 > store.memory.len() as u64 {
                    return Err(ExecError::Trap("out of bounds memory access".into()));
                }
                store.memory[d as usize..(d + n) as usize].fill(val);
            }

            OP_TABLE_GET => {
                let idx = pop_i32(&mut stack) as u32;
                let table_idx = op.imm as usize;
                let shared_table = store.tables.get(table_idx)
                    .ok_or_else(|| ExecError::Trap("undefined table".into()))?;
                let table = shared_table.borrow();
                if idx as usize >= table.len() {
                    return Err(ExecError::Trap("out of bounds table access".into()));
                }
                match table[idx as usize] {
                    Some(func_idx) => stack.push(func_idx as u64),
                    None => stack.push(u64::MAX), // null funcref
                }
            }
            OP_TABLE_SET => {
                let val = pop_raw(&mut stack);
                let idx = pop_i32(&mut stack) as u32;
                let table_idx = op.imm as usize;
                let shared_table = store.tables.get(table_idx)
                    .ok_or_else(|| ExecError::Trap("undefined table".into()))?;
                let mut table = shared_table.borrow_mut();
                if idx as usize >= table.len() {
                    return Err(ExecError::Trap("out of bounds table access".into()));
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
                let n = pop_i32(&mut stack) as u32;
                let init_val = pop_raw(&mut stack);
                let table_idx = op.imm as usize;
                let max = store.table_defs.get(table_idx)
                    .and_then(|(_, max)| *max);
                let shared_table = store.tables.get(table_idx)
                    .ok_or_else(|| ExecError::Trap("undefined table".into()))?;
                let mut table = shared_table.borrow_mut();
                let old_size = table.len() as u32;
                let new_size = old_size as u64 + n as u64;
                // Check max limit
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
                let n = pop_i32(&mut stack) as u32;
                let s = pop_i32(&mut stack) as u32;
                let d = pop_i32(&mut stack) as u32;
                execute_table_copy(store, op.imm_hi() as usize, op.imm_lo() as usize, d, s, n)?;
            }
            OP_TABLE_FILL => {
                let n = pop_i32(&mut stack) as u32;
                let val = pop_raw(&mut stack);
                let i = pop_i32(&mut stack) as u32;
                let table_idx = op.imm as usize;
                let shared_table = store.tables.get(table_idx)
                    .ok_or_else(|| ExecError::Trap("undefined table".into()))?;
                let mut table = shared_table.borrow_mut();
                if i as u64 + n as u64 > table.len() as u64 {
                    return Err(ExecError::Trap("out of bounds table access".into()));
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
}

/// Truncate stack to `height`, preserving the top `arity` values.
/// Avoids Vec allocation by doing an in-place copy.
#[inline(always)]
fn stack_unwind(stack: &mut Vec<u64>, height: usize, arity: usize) {
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

fn do_br(frame: &mut Frame, stack: &mut Vec<u64>, labels: &mut Vec<Label>, depth: u32, steps: &mut u64) -> Result<(), ExecError> {
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
        if *steps > MAX_STEPS {
            return Err(ExecError::Trap("execution limit".into()));
        }
        labels.truncate(label_idx + 1);
        frame.pc = target + 1;
    } else {
        labels.truncate(label_idx);
        frame.pc = target + 1;
    }
    Ok(())
}

