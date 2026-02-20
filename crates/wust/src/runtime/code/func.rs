use crate::runtime::opcode::Op;
use wasmparser::{FuncType, ValType};

/// Pre-compiled function metadata for the new interpreter.
///
/// Unlike the old `Func`, this pre-computes byte offsets for each
/// local variable. With 4-byte slots, i32 locals take 1 slot (4 bytes)
/// while i64 locals take 2 slots (8 bytes), so the compiler must
/// pre-compute where each local lives relative to the locals base.
pub(crate) struct RuntimeFunction {
    /// Index of this function in the program's function table.
    pub func_idx: u32,
    /// Number of times this function has been called (for JIT hotness).
    pub call_count: u32,
    /// Number of parameter values.
    pub params_arity: u32,
    /// Number of result values.
    pub results_arity: u32,
    /// Total number of locals including params.
    pub locals_count: u32,
    /// Total bytes for all locals (sum of slot sizes).
    pub locals_byte_size: u32,
    /// Total bytes for all results in the pre-call area.
    pub results_byte_size: u32,
    /// Byte offset of local[i] from the locals base (after InlineFrame).
    pub local_offsets: Vec<u32>,
    /// Byte size of local[i] (4 for i32/f32, 8 for i64/f64).
    pub local_sizes: Vec<u8>,
    /// Compiled bytecode (same Op format as current interpreter).
    pub body: Vec<Op>,
    /// Out-of-line BrTable data: (targets, default) indexed by Op.imm.
    pub br_tables: Vec<(Vec<u32>, u32)>,
}

/// Returns the byte size of a WASM value type on the unified stack.
///
/// i32, f32, funcref → 4 bytes (1 slot)
/// i64, f64 → 8 bytes (2 slots)
pub(crate) fn val_type_byte_size(ty: &ValType) -> u8 {
    match ty {
        ValType::I32 | ValType::F32 => 4,
        ValType::I64 | ValType::F64 => 8,
        ValType::Ref(_) => 4,
        ValType::V128 => 16,
    }
}

impl RuntimeFunction {
    /// Builds a RuntimeFunction from a parsed Func and its FuncType.
    ///
    /// Pre-computes local byte offsets so the interpreter can access
    /// locals with a single pointer offset instead of indexing.
    ///
    /// `locals` includes params first, then extra locals (same as Func.locals).
    pub(crate) fn from_func(
        func_idx: u32,
        func_type: &FuncType,
        locals: &[ValType],
        body: Vec<Op>,
        br_tables: Vec<(Vec<u32>, u32)>,
    ) -> Self {
        let mut local_offsets = Vec::with_capacity(locals.len());
        let mut local_sizes = Vec::with_capacity(locals.len());
        let mut offset: u32 = 0;

        for local_ty in locals {
            let size = val_type_byte_size(local_ty);
            local_offsets.push(offset);
            local_sizes.push(size);
            offset += size as u32;
        }

        let results_byte_size: u32 = func_type
            .results()
            .iter()
            .map(|ty| val_type_byte_size(ty) as u32)
            .sum();

        Self {
            func_idx,
            call_count: 0,
            params_arity: func_type.params().len() as u32,
            results_arity: func_type.results().len() as u32,
            locals_count: locals.len() as u32,
            locals_byte_size: offset,
            results_byte_size,
            local_offsets,
            local_sizes,
            body,
            br_tables,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn local_offsets_for_mixed_types() {
        // (param i32, param i64, local f32)
        let func_type = FuncType::new(
            vec![ValType::I32, ValType::I64],
            vec![ValType::I32],
        );
        let locals = vec![ValType::I32, ValType::I64, ValType::F32];

        let rf = RuntimeFunction::from_func(
            0,
            &func_type,
            &locals,
            Vec::new(),
            Vec::new(),
        );

        assert_eq!(rf.local_offsets, vec![0, 4, 12]);
        assert_eq!(rf.local_sizes, vec![4, 8, 4]);
        assert_eq!(rf.locals_byte_size, 16);
        assert_eq!(rf.params_arity, 2);
        assert_eq!(rf.results_arity, 1);
        assert_eq!(rf.results_byte_size, 4);
    }

    #[test]
    fn local_offsets_all_i32() {
        let func_type = FuncType::new(
            vec![ValType::I32, ValType::I32],
            vec![],
        );
        let locals = vec![ValType::I32, ValType::I32, ValType::I32];

        let rf = RuntimeFunction::from_func(0, &func_type, &locals, Vec::new(), Vec::new());

        assert_eq!(rf.local_offsets, vec![0, 4, 8]);
        assert_eq!(rf.local_sizes, vec![4, 4, 4]);
        assert_eq!(rf.locals_byte_size, 12);
        assert_eq!(rf.results_byte_size, 0);
    }

    #[test]
    fn local_offsets_all_i64() {
        let func_type = FuncType::new(
            vec![ValType::I64],
            vec![ValType::I64],
        );
        let locals = vec![ValType::I64, ValType::I64];

        let rf = RuntimeFunction::from_func(0, &func_type, &locals, Vec::new(), Vec::new());

        assert_eq!(rf.local_offsets, vec![0, 8]);
        assert_eq!(rf.local_sizes, vec![8, 8]);
        assert_eq!(rf.locals_byte_size, 16);
        assert_eq!(rf.results_byte_size, 8);
    }

    #[test]
    fn no_locals_no_params() {
        let func_type = FuncType::new(vec![], vec![]);
        let locals: Vec<ValType> = vec![];

        let rf = RuntimeFunction::from_func(0, &func_type, &locals, Vec::new(), Vec::new());

        assert_eq!(rf.local_offsets, Vec::<u32>::new());
        assert_eq!(rf.local_sizes, Vec::<u8>::new());
        assert_eq!(rf.locals_byte_size, 0);
        assert_eq!(rf.results_byte_size, 0);
        assert_eq!(rf.params_arity, 0);
        assert_eq!(rf.results_arity, 0);
    }
}
