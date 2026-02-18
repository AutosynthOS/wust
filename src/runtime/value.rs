/// A WASM runtime value.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Value {
    I32(i32),
    I64(i64),
    F32(f32),
    F64(f64),
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

    pub fn default_for(ty: wasmparser::ValType) -> Self {
        match ty {
            wasmparser::ValType::I32 => Value::I32(0),
            wasmparser::ValType::I64 => Value::I64(0),
            wasmparser::ValType::F32 => Value::F32(0.0),
            wasmparser::ValType::F64 => Value::F64(0.0),
            wasmparser::ValType::Ref(r) if r.heap_type() == wasmparser::HeapType::FUNC => {
                Value::FuncRef(None)
            }
            _ => todo!("unsupported type: {:?}", ty),
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
        }
    }
}
