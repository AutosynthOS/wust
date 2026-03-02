use wasmparser::{RefType, ValType};

/// Dynamic WASM value for untyped function calls.
#[derive(Debug, Clone)]
pub enum Val {
    I32(i32),
    I64(i64),
    F32(f32),
    F64(f64),
    V128(u128),
    Ref(RefType),
}

/// Convert a single Rust value to/from a `Val`.
pub trait WasmVal: Sized {
    fn to_val(&self) -> Val;
    fn from_val(val: &Val) -> Result<Self, anyhow::Error>;
}

impl WasmVal for i32 {
    fn to_val(&self) -> Val {
        Val::I32(*self)
    }
    fn from_val(val: &Val) -> Result<Self, anyhow::Error> {
        match val {
            Val::I32(v) => Ok(*v),
            _ => anyhow::bail!("expected i32, got {val:?}"),
        }
    }
}

impl WasmVal for i64 {
    fn to_val(&self) -> Val {
        Val::I64(*self)
    }
    fn from_val(val: &Val) -> Result<Self, anyhow::Error> {
        match val {
            Val::I64(v) => Ok(*v),
            _ => anyhow::bail!("expected i64, got {val:?}"),
        }
    }
}

impl WasmVal for f32 {
    fn to_val(&self) -> Val {
        Val::F32(*self)
    }
    fn from_val(val: &Val) -> Result<Self, anyhow::Error> {
        match val {
            Val::F32(v) => Ok(*v),
            _ => anyhow::bail!("expected f32, got {val:?}"),
        }
    }
}

impl WasmVal for f64 {
    fn to_val(&self) -> Val {
        Val::F64(*self)
    }
    fn from_val(val: &Val) -> Result<Self, anyhow::Error> {
        match val {
            Val::F64(v) => Ok(*v),
            _ => anyhow::bail!("expected f64, got {val:?}"),
        }
    }
}

/// Convert Rust types into WASM call arguments.
pub trait WasmArgs {
    fn to_vals(&self) -> Vec<Val>;
}

/// Convert WASM results back into Rust types.
pub trait WasmResults: Sized {
    fn from_vals(vals: &[Val]) -> Result<Self, anyhow::Error>;
}

impl WasmArgs for () {
    fn to_vals(&self) -> Vec<Val> {
        vec![]
    }
}

impl WasmResults for () {
    fn from_vals(vals: &[Val]) -> Result<Self, anyhow::Error> {
        anyhow::ensure!(vals.is_empty(), "expected no results, got {}", vals.len());
        Ok(())
    }
}

macro_rules! impl_wasm_tuples {
    ($(($($T:ident),+)),* $(,)?) => {
        $(
            impl<$($T: WasmVal),+> WasmArgs for ($($T,)+) {
                #[allow(non_snake_case)]
                fn to_vals(&self) -> Vec<Val> {
                    let ($($T,)+) = self;
                    vec![$($T.to_val()),+]
                }
            }

            impl<$($T: WasmVal),+> WasmResults for ($($T,)+) {
                #[allow(non_snake_case)]
                fn from_vals(vals: &[Val]) -> Result<Self, anyhow::Error> {
                    impl_wasm_tuples!(@destructure vals, $($T),+)
                }
            }
        )*
    };

    (@destructure $vals:ident, $($T:ident),+) => {{
        let expected = impl_wasm_tuples!(@count $($T),+);
        anyhow::ensure!(
            $vals.len() == expected,
            "expected {} results, got {}",
            expected,
            $vals.len()
        );
        let mut _i = 0;
        Ok(($({
            let v = $T::from_val(&$vals[_i])?;
            _i += 1;
            v
        },)+))
    }};

    (@count $($T:ident),+) => {
        <[()]>::len(&[$(impl_wasm_tuples!(@unit $T)),+])
    };

    (@unit $T:ident) => { () };
}

impl_wasm_tuples!(
    (A),
    (A, B),
    (A, B, C),
    (A, B, C, D),
    (A, B, C, D, E),
    (A, B, C, D, E, F),
    (A, B, C, D, E, F, G),
    (A, B, C, D, E, F, G, H),
    (A, B, C, D, E, F, G, H, I),
    (A, B, C, D, E, F, G, H, I, J),
    (A, B, C, D, E, F, G, H, I, J, K),
    (A, B, C, D, E, F, G, H, I, J, K, L),
    (A, B, C, D, E, F, G, H, I, J, K, L, M),
    (A, B, C, D, E, F, G, H, I, J, K, L, M, N),
    (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O),
    (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P),
);

impl Val {
    pub fn zero_for(ty: &ValType) -> Val {
        match ty {
            ValType::I32 => Val::I32(0i32),
            ValType::I64 => Val::I64(0i64),
            ValType::F32 => Val::F32(0.0f32),
            ValType::F64 => Val::F64(0.0f64),
            ValType::V128 => Val::V128(0u128),
            ValType::Ref(ref_ty) => Val::Ref(*ref_ty),
        }
    }

    pub fn size_of(&self) -> usize {
        match self {
            Val::I32(..) => 4,
            Val::I64(..) => 8,
            Val::F32(..) => 4,
            Val::F64(..) => 8,
            Val::V128(..) => 16,
            Val::Ref(..) => todo!(),
        }
    }
}
