use std::fmt;

use super::op::OpCode;

impl fmt::Display for OpCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.wasm_name())
    }
}

impl OpCode {
    /// Returns the canonical wasm text-format name for this opcode.
    pub fn wasm_name(self) -> &'static str {
        match self {
            Self::DataStream => "data_stream",
            Self::Nop => "nop",
            Self::Unreachable => "unreachable",
            Self::Return => "return",
            // i32 arithmetic
            Self::I32Add => "i32.add",
            Self::I32Sub => "i32.sub",
            Self::I32Mul => "i32.mul",
            Self::I32DivS => "i32.div_s",
            Self::I32DivU => "i32.div_u",
            Self::I32RemS => "i32.rem_s",
            Self::I32RemU => "i32.rem_u",
            // i32 bitwise
            Self::I32And => "i32.and",
            Self::I32Or => "i32.or",
            Self::I32Xor => "i32.xor",
            Self::I32Shl => "i32.shl",
            Self::I32ShrS => "i32.shr_s",
            Self::I32ShrU => "i32.shr_u",
            Self::I32Rotl => "i32.rotl",
            Self::I32Rotr => "i32.rotr",
            // i32 comparison / test
            Self::I32Eqz => "i32.eqz",
            Self::I32Eq => "i32.eq",
            Self::I32Ne => "i32.ne",
            Self::I32LtS => "i32.lt_s",
            Self::I32LtU => "i32.lt_u",
            Self::I32GtS => "i32.gt_s",
            Self::I32GtU => "i32.gt_u",
            Self::I32LeS => "i32.le_s",
            Self::I32LeU => "i32.le_u",
            Self::I32GeS => "i32.ge_s",
            Self::I32GeU => "i32.ge_u",
            // i32 unary
            Self::I32Clz => "i32.clz",
            Self::I32Ctz => "i32.ctz",
            Self::I32Popcnt => "i32.popcnt",
            // i32 conversion
            Self::I32WrapI64 => "i32.wrap_i64",
            Self::I32Extend8S => "i32.extend8_s",
            Self::I32Extend16S => "i32.extend16_s",
            // i32 truncation (trapping)
            Self::I32TruncF32S => "i32.trunc_f32_s",
            Self::I32TruncF32U => "i32.trunc_f32_u",
            Self::I32TruncF64S => "i32.trunc_f64_s",
            Self::I32TruncF64U => "i32.trunc_f64_u",
            // i32 truncation (saturating)
            Self::I32TruncSatF32S => "i32.trunc_sat_f32_s",
            Self::I32TruncSatF32U => "i32.trunc_sat_f32_u",
            Self::I32TruncSatF64S => "i32.trunc_sat_f64_s",
            Self::I32TruncSatF64U => "i32.trunc_sat_f64_u",
            // i32 reinterpret
            Self::I32ReinterpretF32 => "i32.reinterpret_f32",
            // i64 arithmetic
            Self::I64Add => "i64.add",
            Self::I64Sub => "i64.sub",
            Self::I64Mul => "i64.mul",
            Self::I64DivS => "i64.div_s",
            Self::I64DivU => "i64.div_u",
            Self::I64RemS => "i64.rem_s",
            Self::I64RemU => "i64.rem_u",
            // i64 bitwise
            Self::I64And => "i64.and",
            Self::I64Or => "i64.or",
            Self::I64Xor => "i64.xor",
            Self::I64Shl => "i64.shl",
            Self::I64ShrS => "i64.shr_s",
            Self::I64ShrU => "i64.shr_u",
            Self::I64Rotl => "i64.rotl",
            Self::I64Rotr => "i64.rotr",
            // i64 comparison / test
            Self::I64Eqz => "i64.eqz",
            Self::I64Eq => "i64.eq",
            Self::I64Ne => "i64.ne",
            Self::I64LtS => "i64.lt_s",
            Self::I64LtU => "i64.lt_u",
            Self::I64GtS => "i64.gt_s",
            Self::I64GtU => "i64.gt_u",
            Self::I64LeS => "i64.le_s",
            Self::I64LeU => "i64.le_u",
            Self::I64GeS => "i64.ge_s",
            Self::I64GeU => "i64.ge_u",
            // i64 unary
            Self::I64Clz => "i64.clz",
            Self::I64Ctz => "i64.ctz",
            Self::I64Popcnt => "i64.popcnt",
            // i64 conversion
            Self::I64ExtendI32S => "i64.extend_i32_s",
            Self::I64ExtendI32U => "i64.extend_i32_u",
            Self::I64Extend8S => "i64.extend8_s",
            Self::I64Extend16S => "i64.extend16_s",
            Self::I64Extend32S => "i64.extend32_s",
            // i64 truncation (trapping)
            Self::I64TruncF32S => "i64.trunc_f32_s",
            Self::I64TruncF32U => "i64.trunc_f32_u",
            Self::I64TruncF64S => "i64.trunc_f64_s",
            Self::I64TruncF64U => "i64.trunc_f64_u",
            // i64 truncation (saturating)
            Self::I64TruncSatF32S => "i64.trunc_sat_f32_s",
            Self::I64TruncSatF32U => "i64.trunc_sat_f32_u",
            Self::I64TruncSatF64S => "i64.trunc_sat_f64_s",
            Self::I64TruncSatF64U => "i64.trunc_sat_f64_u",
            // i64 reinterpret
            Self::I64ReinterpretF64 => "i64.reinterpret_f64",
            // f32 arithmetic (binary)
            Self::F32Add => "f32.add",
            Self::F32Sub => "f32.sub",
            Self::F32Mul => "f32.mul",
            Self::F32Div => "f32.div",
            Self::F32Min => "f32.min",
            Self::F32Max => "f32.max",
            Self::F32Copysign => "f32.copysign",
            // f32 arithmetic (unary)
            Self::F32Abs => "f32.abs",
            Self::F32Neg => "f32.neg",
            Self::F32Sqrt => "f32.sqrt",
            Self::F32Ceil => "f32.ceil",
            Self::F32Floor => "f32.floor",
            Self::F32Trunc => "f32.trunc",
            Self::F32Nearest => "f32.nearest",
            // f32 comparison
            Self::F32Eq => "f32.eq",
            Self::F32Ne => "f32.ne",
            Self::F32Lt => "f32.lt",
            Self::F32Gt => "f32.gt",
            Self::F32Le => "f32.le",
            Self::F32Ge => "f32.ge",
            // f32 conversion
            Self::F32ConvertI32S => "f32.convert_i32_s",
            Self::F32ConvertI32U => "f32.convert_i32_u",
            Self::F32ConvertI64S => "f32.convert_i64_s",
            Self::F32ConvertI64U => "f32.convert_i64_u",
            Self::F32DemoteF64 => "f32.demote_f64",
            Self::F32ReinterpretI32 => "f32.reinterpret_i32",
            // f64 arithmetic (binary)
            Self::F64Add => "f64.add",
            Self::F64Sub => "f64.sub",
            Self::F64Mul => "f64.mul",
            Self::F64Div => "f64.div",
            Self::F64Min => "f64.min",
            Self::F64Max => "f64.max",
            Self::F64Copysign => "f64.copysign",
            // f64 arithmetic (unary)
            Self::F64Abs => "f64.abs",
            Self::F64Neg => "f64.neg",
            Self::F64Sqrt => "f64.sqrt",
            Self::F64Ceil => "f64.ceil",
            Self::F64Floor => "f64.floor",
            Self::F64Trunc => "f64.trunc",
            Self::F64Nearest => "f64.nearest",
            // f64 comparison
            Self::F64Eq => "f64.eq",
            Self::F64Ne => "f64.ne",
            Self::F64Lt => "f64.lt",
            Self::F64Gt => "f64.gt",
            Self::F64Le => "f64.le",
            Self::F64Ge => "f64.ge",
            // f64 conversion
            Self::F64ConvertI32S => "f64.convert_i32_s",
            Self::F64ConvertI32U => "f64.convert_i32_u",
            Self::F64ConvertI64S => "f64.convert_i64_s",
            Self::F64ConvertI64U => "f64.convert_i64_u",
            Self::F64PromoteF32 => "f64.promote_f32",
            Self::F64ReinterpretI64 => "f64.reinterpret_i64",
            // f32/f64 constants
            Self::F32Const => "f32.const",
            Self::F64Const => "f64.const",
            // stack manipulation
            Self::Drop => "drop",
            Self::Select => "select",
            // reference
            Self::RefNull => "ref.null",
            // immediates
            Self::I32Const => "i32.const",
            Self::I64Const => "i64.const",
            Self::LocalGet => "local.get",
            Self::LocalSet => "local.set",
            Self::LocalTee => "local.tee",
            Self::LocalGetI32 => "local.get.i32",
            Self::LocalSetI32 => "local.set.i32",
            Self::LocalTeeI32 => "local.tee.i32",
            Self::LocalGetI64 => "local.get.i64",
            Self::LocalSetI64 => "local.set.i64",
            Self::LocalTeeI64 => "local.tee.i64",
            Self::GlobalGet => "global.get",
            Self::GlobalSet => "global.set",
            Self::Call => "call",
            // control flow
            Self::Block => "block",
            Self::Loop => "loop",
            Self::If => "if",
            Self::Else => "else",
            Self::End => "end",
            Self::Br => "br",
            Self::BrIf => "br_if",
        }
    }
}
