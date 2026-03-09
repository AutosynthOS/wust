//! Conversions between wasm types and autosynth IR types.

use std::collections::HashMap;

use autosynth_ir::{Abi, FunctionIdx, FunctionSignature, IrType};

use wust_core::{FuncMeta, ParsedModule, ValType};

use autosynth_codegen::Width;

/// Convert a wasm [`ValType`] to an [`IrType`].
pub fn to_ir_type(ty: &ValType) -> IrType {
    match ty {
        ValType::I32 => IrType::I32,
        ValType::I64 => IrType::I64,
        _ => todo!("to_ir_type({ty:?}): floats/simd not yet supported"),
    }
}

/// Convert a wasm [`ValType`] to a register [`Width`].
pub fn valtype_to_width(ty: &ValType) -> Width {
    match ty {
        ValType::I32 => Width::W32,
        ValType::I64 => Width::W64,
        ValType::F32 => todo!("F32: needs float register class"),
        ValType::F64 => todo!("F64: needs float register class"),
        ValType::V128 => todo!("V128: needs vector register class"),
        ValType::Ref(_) => todo!("Ref types not yet supported"),
    }
}

/// Build a [`FunctionSignature`] from a wasm [`FuncMeta`].
pub fn func_signature(func: &FuncMeta) -> FunctionSignature {
    FunctionSignature {
        abi: Abi::NativeWasm,
        params: func.params.iter().map(to_ir_type).collect(),
        results: func.results.iter().map(to_ir_type).collect(),
    }
}

/// Build the signature map for all functions in a module.
pub fn build_signatures(module: &ParsedModule) -> HashMap<FunctionIdx, FunctionSignature> {
    module
        .funcs
        .iter()
        .enumerate()
        .map(|(i, func)| (FunctionIdx::User(i as u32), func_signature(func)))
        .collect()
}
