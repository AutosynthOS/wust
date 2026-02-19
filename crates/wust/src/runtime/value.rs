/// A WASM runtime value.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Value {
    I32(i32),
    I64(i64),
    F32(f32),
    F64(f64),
    V128(u128),
    /// Function reference: Some(func_idx) or None (ref.null func).
    FuncRef(Option<u32>),
}

impl Value {
    pub fn unwrap_i32(self) -> i32 {
        match self {
            Value::I32(v) => v,
            _ => panic!("expected i32, got {:?}", self),
        }
    }

    pub fn unwrap_i64(self) -> i64 {
        match self {
            Value::I64(v) => v,
            _ => panic!("expected i64, got {:?}", self),
        }
    }

    pub fn unwrap_f32(self) -> f32 {
        match self {
            Value::F32(v) => v,
            _ => panic!("expected f32, got {:?}", self),
        }
    }

    pub fn unwrap_f64(self) -> f64 {
        match self {
            Value::F64(v) => v,
            _ => panic!("expected f64, got {:?}", self),
        }
    }

    pub fn default_for(ty: wasmparser::ValType) -> Result<Self, String> {
        match ty {
            wasmparser::ValType::I32 => Ok(Value::I32(0)),
            wasmparser::ValType::I64 => Ok(Value::I64(0)),
            wasmparser::ValType::F32 => Ok(Value::F32(0.0)),
            wasmparser::ValType::F64 => Ok(Value::F64(0.0)),
            wasmparser::ValType::V128 => Ok(Value::V128(0)),
            wasmparser::ValType::Ref(r) if r.heap_type() == wasmparser::HeapType::FUNC => {
                Ok(Value::FuncRef(None))
            }
            _ => Err(format!("unsupported value type: {:?}", ty)),
        }
    }

    /// Returns the `wasmparser::ValType` corresponding to this Value variant.
    #[inline(always)]
    pub fn val_type(&self) -> wasmparser::ValType {
        match self {
            Value::I32(_) => wasmparser::ValType::I32,
            Value::I64(_) => wasmparser::ValType::I64,
            Value::F32(_) => wasmparser::ValType::F32,
            Value::F64(_) => wasmparser::ValType::F64,
            Value::V128(_) => wasmparser::ValType::V128,
            Value::FuncRef(_) => wasmparser::ValType::Ref(wasmparser::RefType::FUNCREF),
        }
    }

    /// Reconstruct a Value from raw u64 bits and a type tag (inverse of `to_bits()`).
    #[inline(always)]
    pub fn from_bits(bits: u64, ty: wasmparser::ValType) -> Self {
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

    /// Pack a Value into a raw u64 for the untyped stack.
    #[inline(always)]
    pub fn to_bits(self) -> u64 {
        match self {
            Value::I32(v) => v as u32 as u64,
            Value::I64(v) => v as u64,
            Value::F32(v) => v.to_bits() as u64,
            Value::F64(v) => v.to_bits(),
            Value::FuncRef(Some(idx)) => idx as u64,
            Value::FuncRef(None) => u64::MAX,
            Value::V128(v) => panic!("tried to pack V128 value into u64: {:?}", v),
        }
    }
}
