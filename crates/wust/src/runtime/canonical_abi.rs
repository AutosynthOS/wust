//! Canonical ABI lifting and lowering for the component model.
//!
//! **Lifting** converts core wasm values (i32, i64, f32, f64) into
//! component-level values (bool, char, string, etc.) based on the
//! declared component function type.
//!
//! **Lowering** converts component-level arguments into core wasm values,
//! allocating linear memory via realloc for list/string types.

use std::rc::Rc;

use crate::runtime::component::{
    ComponentArg, ComponentResultType, ComponentValue, CoreInstance, StringEncoding,
};
use crate::runtime::exec;
use crate::runtime::module::Module;
use crate::runtime::store::SharedStore;
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
        ComponentResultType::String => lift_string_result(values, core_instances, memory_instance),
        ComponentResultType::Unit => Ok(Vec::new()),
        _ => values.iter().map(|v| lift_value(*v, result_type)).collect(),
    }
}

/// Lift a core wasm value into a component value based on the declared type.
///
/// Applies masking, sign extension, and type conversion per the canonical ABI.
/// Returns an error (trap) for invalid values like out-of-range char code points.
fn lift_value(v: Value, result_type: ComponentResultType) -> Result<ComponentValue, String> {
    Ok(match (v, result_type) {
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
        (Value::I32(x), ComponentResultType::Char) => char::from_u32(x as u32)
            .map(ComponentValue::Char)
            .ok_or_else(|| format!("invalid char code point: {:#x}", x as u32))?,
        // Fallback: pass through as S32/S64
        (Value::I32(x), _) => ComponentValue::S32(x),
        (Value::I64(x), _) => ComponentValue::S64(x),
        (Value::F32(x), _) => ComponentValue::F32(x),
        (Value::F64(x), _) => ComponentValue::F64(x),
        _ => return Err("unimplemented".into()),
    })
}

/// Lift a string result from linear memory.
///
/// The core function returns a single i32 which is a pointer to a
/// `{ptr: u32, len: u32}` struct in linear memory. We read the struct,
/// validate bounds, and decode the bytes as UTF-8.
///
/// Borrows the store's memory only for the duration of the read,
/// avoiding a full clone of linear memory.
fn lift_string_result(
    values: &[Value],
    core_instances: &[CoreInstance],
    memory_instance: Option<usize>,
) -> Result<Vec<ComponentValue>, String> {
    let retptr = extract_retptr(values)?;
    let s = read_string_from_memory(core_instances, memory_instance, retptr)?;
    Ok(vec![ComponentValue::String(s)])
}

/// Extract the return pointer (i32) from core function results.
fn extract_retptr(values: &[Value]) -> Result<u32, String> {
    match values.first() {
        Some(Value::I32(retptr)) => Ok(*retptr as u32),
        _ => Err("string-returning function did not return an i32".into()),
    }
}

/// Read a UTF-8 string from linear memory at the given return pointer.
///
/// Borrows the store's memory, reads the `(ptr, len)` descriptor at
/// `retptr`, then decodes the string bytes -- all while the borrow is
/// active. Only the resulting `String` is returned, avoiding a full
/// clone of linear memory.
fn read_string_from_memory(
    core_instances: &[CoreInstance],
    memory_instance: Option<usize>,
    retptr: u32,
) -> Result<String, String> {
    let inst_idx = memory_instance.ok_or("string result requires a memory option on canon lift")?;
    match core_instances.get(inst_idx) {
        Some(CoreInstance::Instantiated { store, .. }) => {
            let store = store.borrow();
            let memory = &store.memory;
            let (ptr, len) = read_string_descriptor(memory, retptr)?;
            read_utf8_string(memory, ptr, len)
        }
        _ => Err(format!("memory instance {} not available", inst_idx)),
    }
}

/// Read the `(ptr: u32, len: u32)` descriptor from memory at `retptr`.
///
/// Validates alignment (retptr must be 4-byte aligned) and bounds.
fn read_string_descriptor(memory: &[u8], retptr: u32) -> Result<(u32, u32), String> {
    if retptr % 4 != 0 {
        return Err(format!(
            "unaligned pointer: retptr {retptr:#x} is not 4-byte aligned"
        ));
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
    String::from_utf8(bytes.to_vec()).map_err(|e| format!("invalid UTF-8 in string: {e}"))
}

// ---------------------------------------------------------------------------
// Fused adapter: pointer alignment and bounds validation
// ---------------------------------------------------------------------------

/// Validate fused adapter arguments before calling the callee.
///
/// Checks:
/// - If the result is a compound type (tuple/record), the last arg is the
///   caller's retptr and must be aligned to the type's alignment.
/// - If any param is a compound type, the corresponding arg (argptr) must
///   be aligned.
/// - If any param is a string and the caller uses UTF-16 or latin1+utf16
///   encoding, the string pointer must be 2-byte aligned.
/// - String content must be within the caller's memory bounds.
pub(crate) fn validate_fused_args(
    args: &[Value],
    param_types: &[ComponentResultType],
    result_type: ComponentResultType,
    caller_mem: &[u8],
    caller_string_encoding: StringEncoding,
    callee_has_realloc: bool,
) -> Result<(), String> {
    validate_caller_retptr(args, result_type)?;
    validate_caller_argptr(args, param_types, callee_has_realloc)?;
    validate_caller_string_args(args, param_types, caller_mem, caller_string_encoding)?;
    Ok(())
}

/// Validate fused adapter results after the callee returns.
///
/// If the result is a compound type, the callee's return value is a retptr
/// that must be aligned to the type's alignment.
pub(crate) fn validate_fused_results(
    results: &[Value],
    result_type: ComponentResultType,
) -> Result<(), String> {
    if let ComponentResultType::Compound { alignment } = result_type {
        if let Some(Value::I32(retptr)) = results.first() {
            let ptr = *retptr as u32;
            if ptr % alignment != 0 {
                return Err(format!(
                    "unaligned pointer: callee retptr {ptr:#x} is not {alignment}-byte aligned"
                ));
            }
        }
    }
    Ok(())
}

/// Validate the callee's argptr by calling realloc for compound params.
///
/// When the callee's `canon lift` has a realloc and the params include a
/// compound type, the fused adapter must call realloc to allocate space in
/// the callee's memory. If realloc returns a misaligned pointer, we trap.
pub(crate) fn validate_callee_argptr(
    param_types: &[ComponentResultType],
    realloc_func_index: Option<u32>,
    module: &Rc<Module>,
    store: &SharedStore,
) -> Result<(), String> {
    let Some(realloc_idx) = realloc_func_index else {
        return Ok(());
    };

    // Determine alignment from the compound param type. If the type is
    // Unknown (e.g. an outer-aliased tuple type that wasn't resolved during
    // parsing), default to 4-byte alignment when realloc is present -- only
    // compound types need realloc for params.
    let alignment = param_types.iter().find_map(|p| match p {
        ComponentResultType::Compound { alignment } => Some(*alignment),
        ComponentResultType::Unknown => Some(4u32),
        _ => None,
    });
    let Some(alignment) = alignment else {
        return Ok(());
    };

    // Call realloc(0, 0, alignment, byte_size) to allocate space in the
    // callee's memory. The byte_size doesn't matter for alignment validation;
    // we just need the returned pointer to check alignment.
    let byte_size = alignment * 25;
    let ptr = callee_realloc(module, store, realloc_idx, alignment, byte_size)?;

    if ptr % alignment != 0 {
        return Err(format!(
            "unaligned pointer: callee argptr {ptr:#x} is not {alignment}-byte aligned"
        ));
    }

    Ok(())
}

/// Validate the caller's retptr argument for compound result types.
///
/// When a function returns a compound type, `canon lower` adds a retptr
/// as the last argument. This pointer must be aligned to the result type's
/// alignment.
fn validate_caller_retptr(args: &[Value], result_type: ComponentResultType) -> Result<(), String> {
    if let ComponentResultType::Compound { alignment } = result_type {
        if let Some(Value::I32(retptr)) = args.last() {
            let ptr = *retptr as u32;
            if ptr % alignment != 0 {
                return Err(format!(
                    "unaligned pointer: caller retptr {ptr:#x} is not {alignment}-byte aligned"
                ));
            }
        }
    }
    Ok(())
}

/// Validate the caller's argptr for compound parameter types.
///
/// When a function has compound params (too many to pass flat), `canon lower`
/// passes a single argptr. This pointer must be aligned to the param type's
/// alignment.
fn validate_caller_argptr(
    args: &[Value],
    param_types: &[ComponentResultType],
    callee_has_realloc: bool,
) -> Result<(), String> {
    // If there's exactly one param type and it's Compound (or Unknown with
    // a single arg and the callee has realloc, indicating a compound type
    // passed via argptr), and there's exactly one arg, that arg is the argptr.
    if param_types.len() == 1 {
        let alignment = match param_types[0] {
            ComponentResultType::Compound { alignment } => Some(alignment),
            // Unknown with a single i32 arg and callee realloc strongly
            // suggests a compound type passed via argptr (e.g. an
            // outer-aliased tuple type).
            ComponentResultType::Unknown if args.len() == 1 && callee_has_realloc => Some(4u32),
            _ => None,
        };
        if let Some(alignment) = alignment {
            if args.len() == 1 {
                if let Some(Value::I32(argptr)) = args.first() {
                    let ptr = *argptr as u32;
                    if ptr % alignment != 0 {
                        return Err(format!(
                            "unaligned pointer: caller argptr {ptr:#x} is not {alignment}-byte aligned"
                        ));
                    }
                }
            }
        }
    }
    Ok(())
}

/// Validate string argument pointers for alignment and bounds.
///
/// For each string parameter, the caller passes `(ptr, len)` as two i32
/// args. The pointer must be aligned according to the caller's string
/// encoding (2-byte for UTF-16 and latin1+utf16). The string content
/// must be within the caller's memory bounds.
fn validate_caller_string_args(
    args: &[Value],
    param_types: &[ComponentResultType],
    caller_mem: &[u8],
    caller_string_encoding: StringEncoding,
) -> Result<(), String> {
    let str_alignment = caller_string_encoding.pointer_alignment();
    let mut arg_idx = 0;
    for param_type in param_types {
        if *param_type == ComponentResultType::String {
            // String params use two i32 args: (ptr, len).
            if arg_idx + 1 < args.len() {
                if let (Some(Value::I32(ptr)), Some(Value::I32(len))) =
                    (args.get(arg_idx), args.get(arg_idx + 1))
                {
                    let ptr_u32 = *ptr as u32;
                    let len_u32 = *len as u32;
                    if str_alignment > 1 && ptr_u32 % str_alignment != 0 {
                        return Err(format!(
                            "unaligned pointer: string ptr {ptr_u32:#x} is not {str_alignment}-byte aligned"
                        ));
                    }
                    // Check bounds: ptr + len * char_size must fit in memory.
                    let char_size = match caller_string_encoding {
                        StringEncoding::Utf8 => 1u64,
                        StringEncoding::Utf16 => 2u64,
                        StringEncoding::Latin1Utf16 => 2u64,
                    };
                    let end = (ptr_u32 as u64) + (len_u32 as u64) * char_size;
                    if end > caller_mem.len() as u64 {
                        return Err(format!(
                            "string content out-of-bounds: ptr={ptr_u32:#x} len={len_u32:#x} exceeds memory size {:#x}",
                            caller_mem.len()
                        ));
                    }
                }
                arg_idx += 2;
            }
        } else {
            arg_idx += 1;
        }
    }
    Ok(())
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
            let ty = param_types
                .get(i)
                .copied()
                .unwrap_or(ComponentResultType::Unknown);
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
    results
        .iter()
        .enumerate()
        .map(|(i, v)| {
            // Only normalize the first result value by the declared type.
            // Multi-value results with different types aren't yet supported.
            let ty = if i == 0 {
                result_type
            } else {
                ComponentResultType::Unknown
            };
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
        (Value::I32(x), ComponentResultType::Bool) => Ok(Value::I32(if x != 0 { 1 } else { 0 })),
        (Value::I32(x), ComponentResultType::U8) => Ok(Value::I32((x & 0xFF) as i32)),
        (Value::I32(x), ComponentResultType::S8) => Ok(Value::I32((x as i8) as i32)),
        (Value::I32(x), ComponentResultType::U16) => Ok(Value::I32((x & 0xFFFF) as i32)),
        (Value::I32(x), ComponentResultType::S16) => Ok(Value::I32((x as i16) as i32)),
        (Value::I32(x), ComponentResultType::Char) => char::from_u32(x as u32)
            .map(|c| Value::I32(c as i32))
            .ok_or_else(|| format!("invalid char code point: {:#x}", x as u32)),
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
                let (ptr, len) =
                    lower_list(elements, realloc_func_index, core_instances, instance_index)?;
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
    let realloc_idx =
        realloc_func_index.ok_or("list argument requires a realloc option on canon lift")?;

    let element_count = elements.len() as u32;
    // TODO: list lowering is incomplete — element_size is hardcoded to 1,
    // alignment is hardcoded to 1, and no actual element data is written to
    // the allocated memory. Need to compute real element size/alignment from
    // the component type and serialize each element into the allocation.
    let element_size: u32 = 1;
    let alignment: u32 = 1;
    let byte_length = element_count
        .checked_mul(element_size)
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

    let ptr = callee_realloc(module, shared_store, realloc_idx, alignment, byte_length)?;

    // Validate: ptr + byte_length must not exceed memory size
    let memory_size = shared_store.borrow().memory.len() as u64;
    let end = ptr as u64 + byte_length as u64;
    if end > memory_size {
        return Err("realloc return: beyond end of memory".into());
    }

    Ok((ptr, element_count))
}

// ---------------------------------------------------------------------------
// Fused adapter: memory-based parameter/result transfer
// ---------------------------------------------------------------------------

/// Determine whether the caller is using argptr mode for this call.
///
/// Returns `true` when the number of flat args passed by `canon lower` is
/// fewer than the number of component-level params. This happens when
/// there are too many params to pass flat (>16 i32s), so `canon lower`
/// packs them into linear memory and passes `(argptr [, retptr])`.
pub(crate) fn is_argptr_mode(
    caller_arg_count: usize,
    param_types: &[ComponentResultType],
    result_type: ComponentResultType,
) -> bool {
    if param_types.is_empty() {
        return false;
    }
    // The caller passes argptr as the first arg.
    // If the result is compound, the caller also passes retptr as the last arg.
    let expected_flat = param_types.len()
        + if matches!(result_type, ComponentResultType::Compound { .. }) {
            1
        } else {
            0
        };
    // If caller args < expected flat count, we're in argptr mode.
    // Typically: 1 arg (argptr only) or 2 args (argptr + retptr).
    caller_arg_count < expected_flat && caller_arg_count <= 2
}

/// Read `count` i32 values from memory starting at `ptr`.
///
/// Each value occupies 4 bytes in little-endian format.
/// Returns an error if the read would exceed memory bounds.
pub(crate) fn read_i32s_from_memory(
    memory: &[u8],
    ptr: u32,
    count: usize,
) -> Result<Vec<Value>, String> {
    let byte_len = (count as u64) * 4;
    let end = (ptr as u64) + byte_len;
    if end > memory.len() as u64 {
        return Err(format!(
            "argptr read out-of-bounds: ptr={ptr:#x} count={count} exceeds memory size {:#x}",
            memory.len()
        ));
    }
    let base = ptr as usize;
    let mut values = Vec::with_capacity(count);
    for i in 0..count {
        let offset = base + i * 4;
        let v = i32::from_le_bytes(memory[offset..offset + 4].try_into().unwrap());
        values.push(Value::I32(v));
    }
    Ok(values)
}

/// Write i32 values to memory starting at `ptr`.
///
/// Each value occupies 4 bytes in little-endian format.
/// Returns an error if the write would exceed memory bounds.
pub(crate) fn write_i32s_to_memory(
    memory: &mut [u8],
    ptr: u32,
    values: &[Value],
) -> Result<(), String> {
    let byte_len = (values.len() as u64) * 4;
    let end = (ptr as u64) + byte_len;
    if end > memory.len() as u64 {
        return Err(format!(
            "retptr write out-of-bounds: ptr={ptr:#x} count={} exceeds memory size {:#x}",
            values.len(),
            memory.len()
        ));
    }
    let base = ptr as usize;
    for (i, v) in values.iter().enumerate() {
        let offset = base + i * 4;
        let bytes = match v {
            Value::I32(x) => x.to_le_bytes(),
            Value::F32(x) => x.to_bits().to_le_bytes(),
            _ => 0i32.to_le_bytes(),
        };
        memory[offset..offset + 4].copy_from_slice(&bytes);
    }
    Ok(())
}

/// Call callee's realloc to allocate space for argptr-mode parameters.
///
/// Returns the allocated pointer in the callee's memory.
pub(crate) fn callee_realloc(
    module: &Rc<Module>,
    store: &SharedStore,
    realloc_idx: u32,
    alignment: u32,
    byte_size: u32,
) -> Result<u32, String> {
    let realloc_args = [
        Value::I32(0),
        Value::I32(0),
        Value::I32(alignment as i32),
        Value::I32(byte_size as i32),
    ];
    let results = {
        let mut s = store.borrow_mut();
        exec::call(module, &mut s, realloc_idx, &realloc_args).map_err(|e| format!("trap: {e}"))?
    };
    match results.first() {
        Some(Value::I32(p)) => Ok(*p as u32),
        _ => Err("realloc did not return an i32".into()),
    }
}
