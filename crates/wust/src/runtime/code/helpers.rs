//! Shared helpers for table, memory, and type operations.
//!
//! These are used by the interpreter loop and also by component code.

use crate::runtime::code::module::Module;
use crate::runtime::error::ExecError;
use crate::runtime::store::Store;
use crate::runtime::value::Value;

/// Coerce raw u64 bits to a global Value matching the existing global's type.
pub(crate) fn coerce_bits_to_global(bits: u64, existing: &Value) -> Result<Value, ExecError> {
    match existing {
        Value::V128(_) => Err(ExecError::Trap("v128 globals not supported".into())),
        _ => Ok(Value::from_bits(bits, existing.val_type())),
    }
}

/// Copy elements from an element segment into a table, with bounds checking.
pub(crate) fn execute_table_init(
    store: &mut Store,
    elem_idx: usize,
    table_idx: usize,
    dst: u32,
    src: u32,
    count: u32,
) -> Result<(), ExecError> {
    let seg = store
        .elem_segments
        .get(elem_idx)
        .ok_or_else(|| ExecError::Trap("unknown elem segment".into()))?;
    let elems = match seg {
        None => {
            if count > 0 {
                return Err(ExecError::oob_table());
            }
            return Ok(());
        }
        Some(elems) => {
            if src as usize + count as usize > elems.len() {
                return Err(ExecError::oob_table());
            }
            elems[src as usize..src as usize + count as usize].to_vec()
        }
    };
    let shared_table = store
        .tables
        .get(table_idx)
        .ok_or_else(|| ExecError::Trap("undefined table".into()))?;
    let mut table = shared_table.borrow_mut();
    if dst as usize + count as usize > table.len() {
        return Err(ExecError::oob_table());
    }
    for (i, elem) in elems.iter().enumerate() {
        table[dst as usize + i] = *elem;
    }
    Ok(())
}

/// Copy bytes from a data segment into memory, with bounds checking.
pub(crate) fn execute_memory_init(
    store: &mut Store,
    seg_idx: usize,
    dst: u32,
    src: u32,
    count: u32,
) -> Result<(), ExecError> {
    let seg = store
        .data_segments
        .get(seg_idx)
        .ok_or_else(|| ExecError::Trap("unknown data segment".into()))?;
    match seg {
        None => {
            if count > 0 || src > 0 {
                return Err(ExecError::oob_memory());
            }
        }
        Some(data) => {
            if src as u64 + count as u64 > data.len() as u64 {
                return Err(ExecError::oob_memory());
            }
            if dst as u64 + count as u64 > store.memory.len() as u64 {
                return Err(ExecError::oob_memory());
            }
            let src_copy = data[src as usize..(src + count) as usize].to_vec();
            store.memory[dst as usize..(dst + count) as usize].copy_from_slice(&src_copy);
        }
    }
    Ok(())
}

/// Copy elements between tables (or within the same table), with bounds checking.
pub(crate) fn execute_table_copy(
    store: &mut Store,
    dst_table: usize,
    src_table: usize,
    dst: u32,
    src: u32,
    count: u32,
) -> Result<(), ExecError> {
    let src_len = store
        .tables
        .get(src_table)
        .ok_or_else(|| ExecError::Trap("undefined table".into()))?
        .borrow()
        .len();
    let dst_len = store
        .tables
        .get(dst_table)
        .ok_or_else(|| ExecError::Trap("undefined table".into()))?
        .borrow()
        .len();
    if src as u64 + count as u64 > src_len as u64 || dst as u64 + count as u64 > dst_len as u64 {
        return Err(ExecError::oob_table());
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

/// Look up a function index from a table element.
pub(crate) fn resolve_table_element(
    store: &Store,
    table_idx: u32,
    elem_idx: u32,
) -> Result<u32, ExecError> {
    let shared_table = store
        .tables
        .get(table_idx as usize)
        .ok_or_else(|| ExecError::Trap("undefined table".into()))?;
    let table = shared_table.borrow();
    let entry = table
        .get(elem_idx as usize)
        .ok_or_else(|| ExecError::Trap("undefined element".into()))?;
    entry.ok_or_else(|| ExecError::Trap("uninitialized element".into()))
}

/// Validate that a callee's type matches the expected indirect call type.
pub(crate) fn check_indirect_type(
    module: &Module,
    func_idx: u32,
    expected: &wasmparser::FuncType,
) -> Result<(), ExecError> {
    let callee_type_idx = *module
        .func_types
        .get(func_idx as usize)
        .ok_or_else(|| ExecError::Trap(format!("func type index {} out of bounds", func_idx)))?;
    let callee_type = module
        .types
        .get(callee_type_idx as usize)
        .ok_or_else(|| ExecError::Trap(format!("type index {} out of bounds", callee_type_idx)))?;
    if *callee_type != *expected {
        return Err(ExecError::Trap("indirect call type mismatch".into()));
    }
    Ok(())
}
