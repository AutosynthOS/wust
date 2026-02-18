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
        _ => Ok(values.iter().map(|v| lift_value(*v, result_type)).collect()),
    }
}

/// Lift a core wasm value into a component value based on the declared type.
///
/// Applies masking, sign extension, and type conversion per the canonical ABI.
fn lift_value(v: Value, result_type: ComponentResultType) -> ComponentValue {
    match (v, result_type) {
        (Value::I32(x), ComponentResultType::Bool) => ComponentValue::Bool(x != 0),
        (Value::I32(x), ComponentResultType::U8) => ComponentValue::U8((x as u32) & 0xFF),
        (Value::I32(x), ComponentResultType::S8) => ComponentValue::S8((x as i8) as i32),
        (Value::I32(x), ComponentResultType::U16) => ComponentValue::U16((x as u32) & 0xFFFF),
        (Value::I32(x), ComponentResultType::S16) => ComponentValue::S16((x as i16) as i32),
        (Value::I32(x), ComponentResultType::U32) => ComponentValue::U32(x as u32),
        (Value::I32(x), ComponentResultType::S32) => ComponentValue::S32(x),
        (Value::I64(x), ComponentResultType::U64) => ComponentValue::U64(x as u64),
        (Value::I64(x), ComponentResultType::S64) => ComponentValue::S64(x),
        (Value::F32(x), ComponentResultType::F32) => ComponentValue::F32(x),
        (Value::F64(x), ComponentResultType::F64) => ComponentValue::F64(x),
        (Value::I32(x), ComponentResultType::Char) => {
            ComponentValue::Char(char::from_u32(x as u32).unwrap_or('\u{FFFD}'))
        }
        // Fallback: pass through as S32/S64
        (Value::I32(x), _) => ComponentValue::S32(x),
        (Value::I64(x), _) => ComponentValue::S64(x),
        (Value::F32(x), _) => ComponentValue::F32(x),
        (Value::F64(x), _) => ComponentValue::F64(x),
        _ => ComponentValue::S32(0),
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
    let (ptr, len) = read_string_descriptor(memory, retptr)?;
    let s = read_utf8_string(memory, ptr, len)?;
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
fn get_memory_bytes(
    core_instances: &[CoreInstance],
    memory_instance: Option<usize>,
) -> Result<&[u8], String> {
    let inst_idx = memory_instance
        .ok_or("string result requires a memory option on canon lift")?;
    match core_instances.get(inst_idx) {
        Some(CoreInstance::Instantiated { store, .. }) => Ok(&store.memory),
        _ => Err(format!("memory instance {} not available", inst_idx)),
    }
}

/// Read the `(ptr: u32, len: u32)` descriptor from memory at `retptr`.
fn read_string_descriptor(memory: &[u8], retptr: u32) -> Result<(u32, u32), String> {
    let retptr = retptr as usize;
    if retptr + 8 > memory.len() {
        return Err("string pointer/length out of bounds of memory".into());
    }
    let ptr = u32::from_le_bytes(memory[retptr..retptr + 4].try_into().unwrap());
    let len = u32::from_le_bytes(memory[retptr + 4..retptr + 8].try_into().unwrap());
    Ok((ptr, len))
}

/// Read `len` bytes from memory at `ptr` and decode as UTF-8.
fn read_utf8_string(memory: &[u8], ptr: u32, len: u32) -> Result<String, String> {
    let ptr = ptr as usize;
    let len = len as usize;
    if ptr + len > memory.len() {
        return Err("string pointer/length out of bounds of memory".into());
    }
    let bytes = &memory[ptr..ptr + len];
    String::from_utf8(bytes.to_vec())
        .map_err(|e| format!("invalid UTF-8 in string: {e}"))
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

    let (module, store) = match instance {
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

    let results = exec::call(module, store, realloc_idx, &realloc_args)
        .map_err(|e| format!("trap: {e}"))?;

    let ptr = match results.first() {
        Some(Value::I32(p)) => *p as u32,
        _ => return Err("realloc did not return an i32".into()),
    };

    // Validate: ptr + byte_length must not exceed memory size
    let memory_size = store.memory.len() as u64;
    let end = ptr as u64 + byte_length as u64;
    if end > memory_size {
        return Err("realloc return: beyond end of memory".into());
    }

    Ok((ptr, element_count))
}
