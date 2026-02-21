// Interpreter macros — included via include!() in exec.rs.
//
// These reference `pop_i32`, `pop_i64`, `pop_f32`, `pop_f64`, `pop_raw`
// and `ExecError` from the enclosing scope.

macro_rules! push_i32 {
    ($stack:expr, $v:expr) => {
        $stack.push_u64($v as u32 as u64)
    };
}

macro_rules! push_i64 {
    ($stack:expr, $v:expr) => {
        $stack.push_u64($v as u64)
    };
}

macro_rules! push_f32 {
    ($stack:expr, $v:expr) => {
        $stack.push_u64(($v).to_bits() as u64)
    };
}

macro_rules! push_f64 {
    ($stack:expr, $v:expr) => {
        $stack.push_u64(($v).to_bits())
    };
}

macro_rules! binop_i32 {
    ($stack:expr, $op:expr) => {{
        let b = pop_i32($stack);
        let a = pop_i32($stack);
        push_i32!($stack, $op(a, b));
    }};
}

macro_rules! binop_i64 {
    ($stack:expr, $op:expr) => {{
        let b = pop_i64($stack);
        let a = pop_i64($stack);
        push_i64!($stack, $op(a, b));
    }};
}

macro_rules! binop_f32 {
    ($stack:expr, $op:expr) => {{
        let b = pop_f32($stack);
        let a = pop_f32($stack);
        push_f32!($stack, $op(a, b));
    }};
}

macro_rules! binop_f64 {
    ($stack:expr, $op:expr) => {{
        let b = pop_f64($stack);
        let a = pop_f64($stack);
        push_f64!($stack, $op(a, b));
    }};
}

macro_rules! unop_i32 {
    ($stack:expr, $op:expr) => {{
        let a = pop_i32($stack);
        push_i32!($stack, $op(a));
    }};
}

macro_rules! unop_i64 {
    ($stack:expr, $op:expr) => {{
        let a = pop_i64($stack);
        push_i64!($stack, $op(a));
    }};
}

macro_rules! unop_f32 {
    ($stack:expr, $op:expr) => {{
        let a = pop_f32($stack);
        push_f32!($stack, $op(a));
    }};
}

macro_rules! unop_f64 {
    ($stack:expr, $op:expr) => {{
        let a = pop_f64($stack);
        push_f64!($stack, $op(a));
    }};
}

macro_rules! cmpop_i32 {
    ($stack:expr, $op:expr) => {{
        let b = pop_i32($stack);
        let a = pop_i32($stack);
        push_i32!($stack, if $op(a, b) { 1i32 } else { 0i32 });
    }};
}

macro_rules! cmpop_i64 {
    ($stack:expr, $op:expr) => {{
        let b = pop_i64($stack);
        let a = pop_i64($stack);
        push_i32!($stack, if $op(a, b) { 1i32 } else { 0i32 });
    }};
}

macro_rules! cmpop_f32 {
    ($stack:expr, $op:expr) => {{
        let b = pop_f32($stack);
        let a = pop_f32($stack);
        push_i32!($stack, if $op(a, b) { 1i32 } else { 0i32 });
    }};
}

macro_rules! cmpop_f64 {
    ($stack:expr, $op:expr) => {{
        let b = pop_f64($stack);
        let a = pop_f64($stack);
        push_i32!($stack, if $op(a, b) { 1i32 } else { 0i32 });
    }};
}

macro_rules! mem_load {
    ($stack:expr, $store:expr, $offset:expr, $N:literal, $conv:expr) => {{
        let base = pop_i32($stack) as u32 as u64;
        let bytes = $store
            .memory_load::<$N>(base + $offset)
            .map_err(|e| ExecError::Trap(e.into()))?;
        $stack.push_u64($conv(bytes));
    }};
}

macro_rules! mem_store {
    ($stack:expr, $store:expr, $offset:expr, $pop_fn:ident, $conv:expr) => {{
        let val = $pop_fn($stack);
        let base = pop_i32($stack) as u32 as u64;
        $store
            .memory_store(base + $offset, &$conv(val))
            .map_err(|e| ExecError::Trap(e.into()))?;
    }};
}

macro_rules! div_s {
    ($stack:expr, $pop_fn:ident, $int_ty:ty) => {{
        let b = $pop_fn($stack);
        let a = $pop_fn($stack);
        if b == 0 {
            return Err(ExecError::divide_by_zero());
        }
        if a == <$int_ty>::MIN && b == -1 {
            return Err(ExecError::integer_overflow());
        }
        push_i32!($stack, a.wrapping_div(b));
    }};
}

macro_rules! div_s_i64 {
    ($stack:expr) => {{
        let b = pop_i64($stack);
        let a = pop_i64($stack);
        if b == 0 {
            return Err(ExecError::divide_by_zero());
        }
        if a == i64::MIN && b == -1 {
            return Err(ExecError::integer_overflow());
        }
        push_i64!($stack, a.wrapping_div(b));
    }};
}

macro_rules! div_u_i32 {
    ($stack:expr) => {{
        let b = pop_i32($stack) as u32;
        let a = pop_i32($stack) as u32;
        if b == 0 {
            return Err(ExecError::divide_by_zero());
        }
        push_i32!($stack, (a / b) as i32);
    }};
}

macro_rules! div_u_i64 {
    ($stack:expr) => {{
        let b = pop_i64($stack) as u64;
        let a = pop_i64($stack) as u64;
        if b == 0 {
            return Err(ExecError::divide_by_zero());
        }
        push_i64!($stack, (a / b) as i64);
    }};
}

macro_rules! rem_s_i32 {
    ($stack:expr) => {{
        let b = pop_i32($stack);
        let a = pop_i32($stack);
        if b == 0 {
            return Err(ExecError::divide_by_zero());
        }
        push_i32!(
            $stack,
            if a == i32::MIN && b == -1 {
                0
            } else {
                a.wrapping_rem(b)
            }
        );
    }};
}

macro_rules! rem_s_i64 {
    ($stack:expr) => {{
        let b = pop_i64($stack);
        let a = pop_i64($stack);
        if b == 0 {
            return Err(ExecError::divide_by_zero());
        }
        push_i64!(
            $stack,
            if a == i64::MIN && b == -1 {
                0
            } else {
                a.wrapping_rem(b)
            }
        );
    }};
}

macro_rules! rem_u_i32 {
    ($stack:expr) => {{
        let b = pop_i32($stack) as u32;
        let a = pop_i32($stack) as u32;
        if b == 0 {
            return Err(ExecError::divide_by_zero());
        }
        push_i32!($stack, (a % b) as i32);
    }};
}

macro_rules! rem_u_i64 {
    ($stack:expr) => {{
        let b = pop_i64($stack) as u64;
        let a = pop_i64($stack) as u64;
        if b == 0 {
            return Err(ExecError::divide_by_zero());
        }
        push_i64!($stack, (a % b) as i64);
    }};
}

macro_rules! trunc_op {
    ($stack:expr, $pop_fn:ident, $push_macro:ident, $int_ty:ty, $max_bound:expr, $min_bound:expr) => {{
        let a = $pop_fn($stack);
        if a.is_nan() {
            return Err(ExecError::Trap("invalid conversion to integer".into()));
        }
        if a.is_infinite() {
            return Err(ExecError::integer_overflow());
        }
        let t = a.trunc();
        if t >= $max_bound || t < $min_bound {
            return Err(ExecError::integer_overflow());
        }
        $push_macro!($stack, t as $int_ty);
    }};
}

macro_rules! trunc_op_u {
    ($stack:expr, $pop_fn:ident, $push_macro:ident, $uint_ty:ty, $int_ty:ty, $max_bound:expr) => {{
        let a = $pop_fn($stack);
        if a.is_nan() {
            return Err(ExecError::Trap("invalid conversion to integer".into()));
        }
        if a.is_infinite() {
            return Err(ExecError::integer_overflow());
        }
        let t = a.trunc();
        if t >= $max_bound || t < 0.0 {
            return Err(ExecError::integer_overflow());
        }
        $push_macro!($stack, t as $uint_ty as $int_ty);
    }};
}

macro_rules! trunc_sat_s {
    ($stack:expr, $pop_fn:ident, $push_macro:ident, $int_ty:ty, $max_bound:expr, $min_bound:expr) => {{
        let a = $pop_fn($stack);
        $push_macro!(
            $stack,
            if a.is_nan() {
                0 as $int_ty
            } else if a >= $max_bound {
                <$int_ty>::MAX
            } else if a < $min_bound {
                <$int_ty>::MIN
            } else {
                a as $int_ty
            }
        );
    }};
}

macro_rules! trunc_sat_u {
    ($stack:expr, $pop_fn:ident, $push_macro:ident, $uint_ty:ty, $int_ty:ty, $max_bound:expr) => {{
        let a = $pop_fn($stack);
        $push_macro!(
            $stack,
            if a.is_nan() || a <= -1.0 {
                0 as $uint_ty as $int_ty
            } else if a >= $max_bound {
                <$uint_ty>::MAX as $int_ty
            } else {
                a as $uint_ty as $int_ty
            }
        );
    }};
}
