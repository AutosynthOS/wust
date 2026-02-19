//! Canonical ABI lifting and lowering for the component model.
//!
//! **Lifting** converts core wasm values (i32, i64, f32, f64) into
//! component-level values (bool, char, string, etc.) based on the
//! declared component function type.
//!
//! **Lowering** converts component-level arguments into core wasm values,
//! allocating linear memory via realloc for list/string types.

use crate::runtime::component::{
    ComponentArg, ComponentResultType, ComponentValue, CoreInstance,
};
use crate::runtime::exec;
use crate::runtime::value::Value;

// ---------------------------------------------------------------------------
// Lifting
// ---------------------------------------------------------------------------

/// Lift core wasm results into component values based on the result type.
///
/// Dispatches to string lifting (which reads from linear memory) or scalar
/// lifting (which masks/extends individual values).
pub(crate) fn lift_results(
    values: &[Value],
    result_type: ComponentResultType,
    core_instances: &[CoreInstance],
    memory_instance: Option<usize>,
) -> Result<Vec<ComponentValue>, String> {
    match result_type {
        ComponentResultType::String => {
            lift_string_result(values, core_instances, memory_instance)
        }
        ComponentResultType::Unit => Ok(Vec::new()),
        _ => values.iter().map(|v| lift_value(*v, result_type)).collect(),
    }
}

/// Lift a core wasm value into a component value based on the declared type.
///
/// Applies masking, sign extension, and type conversion per the canonical ABI.
/// Returns an error (trap) for invalid values like out-of-range char code points.
fn lift_value(v: Value, result_type: ComponentResultType) -> Result<ComponentValue, String> {
    match (v, result_type) {
        (Value::I32(x), ComponentResultType::Bool) => Ok(ComponentValue::Bool(x != 0)),
        (Value::I32(x), ComponentResultType::U8) => Ok(ComponentValue::U8((x as u32) & 0xFF)),
        (Value::I32(x), ComponentResultType::S8) => Ok(ComponentValue::S8((x as i8) as i32)),
        (Value::I32(x), ComponentResultType::U16) => Ok(ComponentValue::U16((x as u32) & 0xFFFF)),
        (Value::I32(x), ComponentResultType::S16) => Ok(ComponentValue::S16((x as i16) as i32)),
        (Value::I32(x), ComponentResultType::U32) => Ok(ComponentValue::U32(x as u32)),
        (Value::I32(x), ComponentResultType::S32) => Ok(ComponentValue::S32(x)),
        (Value::I64(x), ComponentResultType::U64) => Ok(ComponentValue::U64(x as u64)),
        (Value::I64(x), ComponentResultType::S64) => Ok(ComponentValue::S64(x)),
        (Value::F32(x), ComponentResultType::F32) => Ok(ComponentValue::F32(x)),
        (Value::F64(x), ComponentResultType::F64) => Ok(ComponentValue::F64(x)),
        (Value::I32(x), ComponentResultType::Char) => {
            char::from_u32(x as u32)
                .map(ComponentValue::Char)
                .ok_or_else(|| format!("invalid char code point: {:#x}", x as u32))
        }
        // Fallback: pass through as S32/S64
        (Value::I32(x), _) => Ok(ComponentValue::S32(x)),
        (Value::I64(x), _) => Ok(ComponentValue::S64(x)),
        (Value::F32(x), _) => Ok(ComponentValue::F32(x)),
        (Value::F64(x), _) => Ok(ComponentValue::F64(x)),
        _ => Ok(ComponentValue::S32(0)),
    }
}

/// Lift a string result from linear memory.
///
/// The core function returns a single i32 which is a pointer to a
/// `{ptr: u32, len: u32}` struct in linear memory. We read the struct,
/// validate bounds, and decode the bytes as UTF-8.
fn lift_string_result(
    values: &[Value],
    core_instances: &[CoreInstance],
    memory_instance: Option<usize>,
) -> Result<Vec<ComponentValue>, String> {
    let retptr = extract_retptr(values)?;
    let memory = get_memory_bytes(core_instances, memory_instance)?;
    let (ptr, len) = read_string_descriptor(&memory, retptr)?;
    let s = read_utf8_string(&memory, ptr, len)?;
    Ok(vec![ComponentValue::String(s)])
}

/// Extract the return pointer (i32) from core function results.
fn extract_retptr(values: &[Value]) -> Result<u32, String> {
    match values.first() {
        Some(Value::I32(retptr)) => Ok(*retptr as u32),
        _ => Err("string-returning function did not return an i32".into()),
    }
}

/// Get the linear memory bytes from the core instance that owns the memory.
///
/// Returns a copy of the memory content because the Store is behind a
/// RefCell and we cannot return a borrow that outlives the RefCell guard.
fn get_memory_bytes(
    core_instances: &[CoreInstance],
    memory_instance: Option<usize>,
) -> Result<Vec<u8>, String> {
    let inst_idx = memory_instance
        .ok_or("string result requires a memory option on canon lift")?;
    match core_instances.get(inst_idx) {
        Some(CoreInstance::Instantiated { store, .. }) => {
            let store = store.borrow();
            Ok(store.memory.clone())
        }
        _ => Err(format!("memory instance {} not available", inst_idx)),
    }
}

/// Read the `(ptr: u32, len: u32)` descriptor from memory at `retptr`.
///
/// Validates alignment (retptr must be 4-byte aligned) and bounds.
fn read_string_descriptor(memory: &[u8], retptr: u32) -> Result<(u32, u32), String> {
    if retptr % 4 != 0 {
        return Err(format!("unaligned pointer: retptr {retptr:#x} is not 4-byte aligned"));
    }
    let retptr = retptr as usize;
    if retptr + 8 > memory.len() {
        return Err("string pointer/length out of bounds of memory".into());
    }
    // Safe: bounds checked above, slices are exactly 4 bytes
    let ptr = u32::from_le_bytes(memory[retptr..retptr + 4].try_into().unwrap());
    let len = u32::from_le_bytes(memory[retptr + 4..retptr + 8].try_into().unwrap());
    Ok((ptr, len))
}

/// Read `len` bytes from memory at `ptr` and decode as UTF-8.
///
/// Validates that `ptr + len` does not overflow and stays within memory bounds.
fn read_utf8_string(memory: &[u8], ptr: u32, len: u32) -> Result<String, String> {
    let end = (ptr as u64) + (len as u64);
    if end > memory.len() as u64 {
        return Err(format!(
            "string content out-of-bounds: ptr={ptr:#x} len={len:#x} exceeds memory size {:#x}",
            memory.len()
        ));
    }
    let bytes = &memory[ptr as usize..(ptr + len) as usize];
    String::from_utf8(bytes.to_vec())
        .map_err(|e| format!("invalid UTF-8 in string: {e}"))
}

// ---------------------------------------------------------------------------
// Fused adapter: normalize args across component boundary
// ---------------------------------------------------------------------------

/// Normalize core wasm arguments through a canonical ABI round-trip.
///
/// For each argument with a known component type, lifts from the caller's
/// core representation to the component type (applying masking, validation),
/// then lowers back to the callee's core representation.
///
/// Returns an error (trap) if any argument is invalid for its declared type
/// (e.g. an out-of-range char code point or an invalid variant discriminant).
pub(crate) fn normalize_args(
    args: &[Value],
    param_types: &[ComponentResultType],
) -> Result<Vec<Value>, String> {
    args.iter()
        .enumerate()
        .map(|(i, v)| {
            let ty = param_types.get(i).copied().unwrap_or(ComponentResultType::Unknown);
            normalize_value(*v, ty)
        })
        .collect()
}

/// Normalize a single core wasm return value through a lift-then-lower round-trip.
///
/// Used for the result type of a cross-component function call.
/// For a single-result function, normalizes `results[0]` according to `result_type`.
pub(crate) fn normalize_result(
    results: &[Value],
    result_type: ComponentResultType,
) -> Result<Vec<Value>, String> {
    if results.is_empty() || result_type == ComponentResultType::Unit {
        return Ok(results.to_vec());
    }
    results.iter()
        .enumerate()
        .map(|(i, v)| {
            // Only normalize the first result value by the declared type.
            // Multi-value results with different types aren't yet supported.
            let ty = if i == 0 { result_type } else { ComponentResultType::Unknown };
            normalize_value(*v, ty)
        })
        .collect()
}

/// Normalize a single core wasm value through a lift-then-lower round-trip.
///
/// For bool: any non-zero -> 1, zero -> 0.
/// For u8/u16: mask to the appropriate bit width.
/// For s8/s16: sign-extend then truncate.
/// For char: validate the code point is a valid Unicode scalar value.
fn normalize_value(v: Value, ty: ComponentResultType) -> Result<Value, String> {
    match (v, ty) {
        (Value::I32(x), ComponentResultType::Bool) => {
            Ok(Value::I32(if x != 0 { 1 } else { 0 }))
        }
        (Value::I32(x), ComponentResultType::U8) => {
            Ok(Value::I32((x & 0xFF) as i32))
        }
        (Value::I32(x), ComponentResultType::S8) => {
            Ok(Value::I32((x as i8) as i32))
        }
        (Value::I32(x), ComponentResultType::U16) => {
            Ok(Value::I32((x & 0xFFFF) as i32))
        }
        (Value::I32(x), ComponentResultType::S16) => {
            Ok(Value::I32((x as i16) as i32))
        }
        (Value::I32(x), ComponentResultType::Char) => {
            char::from_u32(x as u32)
                .map(|c| Value::I32(c as i32))
                .ok_or_else(|| format!("invalid char code point: {:#x}", x as u32))
        }
        (Value::I32(x), ComponentResultType::Variant { case_count }) => {
            let disc = x as u32;
            if disc >= case_count {
                Err(format!(
                    "invalid variant discriminant: {} (expected < {})",
                    disc, case_count
                ))
            } else {
                Ok(v)
            }
        }
        // All other types pass through unchanged.
        _ => Ok(v),
    }
}

// ---------------------------------------------------------------------------
// Lowering
// ---------------------------------------------------------------------------

/// Lower component-level arguments into core wasm values.
///
/// Scalar arguments pass through directly. List arguments are lowered via
/// the canonical ABI: call realloc to allocate space, validate the returned
/// pointer, then pass `(ptr, len)` as two i32 core args.
pub(crate) fn lower_component_args(
    args: &[ComponentArg],
    realloc_func_index: Option<u32>,
    core_instances: &mut [CoreInstance],
    instance_index: usize,
) -> Result<Vec<Value>, String> {
    let mut core_args = Vec::new();
    for arg in args {
        match arg {
            ComponentArg::Value(v) => core_args.push(*v),
            ComponentArg::List(elements) => {
                let (ptr, len) = lower_list(
                    elements,
                    realloc_func_index,
                    core_instances,
                    instance_index,
                )?;
                core_args.push(Value::I32(ptr as i32));
                core_args.push(Value::I32(len as i32));
            }
        }
    }
    Ok(core_args)
}

/// Lower a list argument via the canonical ABI.
///
/// 1. Call realloc(0, 0, alignment, byte_length) to allocate
/// 2. Validate: returned_ptr + byte_length <= memory.len()
/// 3. Return (ptr, element_count)
///
/// For now, element size and alignment are both 1 (sufficient for
/// zero-length lists and byte-sized element types).
fn lower_list(
    elements: &[ComponentArg],
    realloc_func_index: Option<u32>,
    core_instances: &mut [CoreInstance],
    instance_index: usize,
) -> Result<(u32, u32), String> {
    let realloc_idx = realloc_func_index
        .ok_or("list argument requires a realloc option on canon lift")?;

    let element_count = elements.len() as u32;
    // TODO: compute real element size and alignment from the component type
    let element_size: u32 = 1;
    let alignment: u32 = 1;
    let byte_length = element_count.checked_mul(element_size)
        .ok_or("list byte length overflow")?;

    let instance = core_instances
        .get_mut(instance_index)
        .ok_or_else(|| format!("core instance {} out of bounds", instance_index))?;

    let (module, shared_store) = match instance {
        CoreInstance::Instantiated { module, store } => (module, store),
        CoreInstance::Synthetic { .. } => {
            return Err("cannot call realloc on synthetic instance".into());
        }
    };

    let realloc_args = [
        Value::I32(0),                  // original ptr
        Value::I32(0),                  // original size
        Value::I32(alignment as i32),   // alignment
        Value::I32(byte_length as i32), // new size
    ];

    let results = {
        let mut store = shared_store.borrow_mut();
        exec::call(module, &mut store, realloc_idx, &realloc_args)
            .map_err(|e| format!("trap: {e}"))?
    };

    let ptr = match results.first() {
        Some(Value::I32(p)) => *p as u32,
        _ => return Err("realloc did not return an i32".into()),
    };

    // Validate: ptr + byte_length must not exceed memory size
    let memory_size = shared_store.borrow().memory.len() as u64;
    let end = ptr as u64 + byte_length as u64;
    if end > memory_size {
        return Err("realloc return: beyond end of memory".into());
    }

    Ok((ptr, element_count))
}
