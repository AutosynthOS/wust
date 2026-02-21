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
                if bits == u64::MAX {
                    Value::FuncRef(None)
                } else {
                    Value::FuncRef(Some(bits as u32))
                }
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

/// WASM nearest (round ties to even).
pub(crate) fn wasm_nearest<F: Float>(a: F) -> F {
    if a.is_nan() || a.is_infinite() || a.is_zero() {
        return a;
    }
    let trunc = a.float_trunc();
    let frac = a.float_sub(trunc).float_abs();
    if frac.eq_half() {
        // Tie: round to even
        if trunc.is_even() {
            trunc
        } else {
            trunc.float_add(a.float_signum())
        }
    } else if frac.gt_half() {
        trunc.float_add(a.float_signum())
    } else {
        trunc
    }
}

pub(crate) trait Float: Copy {
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
    fn is_nan(self) -> bool {
        self.is_nan()
    }
    fn is_infinite(self) -> bool {
        self.is_infinite()
    }
    fn is_zero(self) -> bool {
        self == 0.0
    }
    fn is_sign_negative(self) -> bool {
        self.is_sign_negative()
    }
    fn is_sign_positive(self) -> bool {
        self.is_sign_positive()
    }
    fn is_even(self) -> bool {
        self % 2.0 == 0.0
    }
    fn eq_half(self) -> bool {
        self == 0.5
    }
    fn gt_half(self) -> bool {
        self > 0.5
    }
    fn float_min(self, other: Self) -> Self {
        self.min(other)
    }
    fn float_max(self, other: Self) -> Self {
        self.max(other)
    }
    fn float_trunc(self) -> Self {
        self.trunc()
    }
    fn float_abs(self) -> Self {
        self.abs()
    }
    fn float_sub(self, other: Self) -> Self {
        self - other
    }
    fn float_add(self, other: Self) -> Self {
        self + other
    }
    fn float_signum(self) -> Self {
        self.signum()
    }
}

impl Float for f64 {
    const NAN: Self = f64::NAN;
    const ZERO: Self = 0.0;
    const NEG_ZERO: Self = -0.0;
    fn is_nan(self) -> bool {
        self.is_nan()
    }
    fn is_infinite(self) -> bool {
        self.is_infinite()
    }
    fn is_zero(self) -> bool {
        self == 0.0
    }
    fn is_sign_negative(self) -> bool {
        self.is_sign_negative()
    }
    fn is_sign_positive(self) -> bool {
        self.is_sign_positive()
    }
    fn is_even(self) -> bool {
        self % 2.0 == 0.0
    }
    fn eq_half(self) -> bool {
        self == 0.5
    }
    fn gt_half(self) -> bool {
        self > 0.5
    }
    fn float_min(self, other: Self) -> Self {
        self.min(other)
    }
    fn float_max(self, other: Self) -> Self {
        self.max(other)
    }
    fn float_trunc(self) -> Self {
        self.trunc()
    }
    fn float_abs(self) -> Self {
        self.abs()
    }
    fn float_sub(self, other: Self) -> Self {
        self - other
    }
    fn float_add(self, other: Self) -> Self {
        self + other
    }
    fn float_signum(self) -> Self {
        self.signum()
    }
}

/// WASM float min with NaN propagation and signed zero handling.
pub(crate) fn wasm_min<F: Float>(a: F, b: F) -> F {
    if a.is_nan() || b.is_nan() {
        F::NAN
    } else if a.is_zero() && b.is_zero() {
        if a.is_sign_negative() || b.is_sign_negative() {
            F::NEG_ZERO
        } else {
            F::ZERO
        }
    } else {
        a.float_min(b)
    }
}

/// WASM float max with NaN propagation and signed zero handling.
pub(crate) fn wasm_max<F: Float>(a: F, b: F) -> F {
    if a.is_nan() || b.is_nan() {
        F::NAN
    } else if a.is_zero() && b.is_zero() {
        if a.is_sign_positive() || b.is_sign_positive() {
            F::ZERO
        } else {
            F::NEG_ZERO
        }
    } else {
        a.float_max(b)
    }
}
