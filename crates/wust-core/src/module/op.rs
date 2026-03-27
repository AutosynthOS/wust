/// An instruction packed into 64 bits: 8-bit opcode + 56-bit immediate.
///
/// On little-endian (ARM64/x86), the opcode sits in byte 0 (low byte)
/// and the immediate occupies bytes 1-7 (bits 8..63).
///
/// Stored as a raw u64 for zero-cost field access in debug builds —
/// avoids the transmute spills that `#[repr(C)]` structs generate
/// without optimization.
#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct InlineOp(u64);

impl InlineOp {
    /// Read the opcode byte as an `OpCode` via pointer cast.
    ///
    /// # Safety
    /// On little-endian, byte 0 of the u64 is the opcode. We only
    /// construct InlineOp from valid OpCode variants during parsing,
    /// so this is always a valid discriminant.
    #[inline(always)]
    pub fn opcode(&self) -> OpCode {
        // SAFETY: byte 0 of the u64 holds a valid OpCode discriminant.
        unsafe { *(&self.0 as *const u64 as *const OpCode) }
    }

    /// Read the raw opcode byte without interpreting it as an OpCode.
    ///
    /// Used by engine-specific fuse passes that pack non-standard opcodes
    /// (≥128) into the same InlineOp layout.
    #[inline(always)]
    pub fn raw_opcode(&self) -> u8 {
        self.0 as u8
    }

    /// Read the immediate as a u32 (lower 24 bits of the immediate field).
    #[inline(always)]
    pub fn immediate_u32(self) -> u32 {
        (self.0 >> 8) as u32
    }

    /// Read the immediate as a sign-extended i32 from the 24-bit field.
    #[inline(always)]
    pub fn immediate_i32(self) -> i32 {
        ((self.0 >> 8) as i32) << 8 >> 8
    }

    /// Raw u64 value (for debugging/dump).
    pub fn raw(self) -> u64 {
        self.0
    }

    /// Construct an InlineOp from a raw u64 value.
    ///
    /// Used by engine-specific fuse passes to pack custom opcodes.
    pub fn from_raw(raw: u64) -> Self {
        Self(raw)
    }

    /// Bits 8-15: first u8 field.
    #[inline(always)]
    pub fn imm_u8_a(self) -> u8 {
        (self.0 >> 8) as u8
    }

    /// Bits 16-23: second u8 field.
    #[inline(always)]
    pub fn imm_u8_b(self) -> u8 {
        (self.0 >> 16) as u8
    }

    /// Bits 24-31: third u8 field.
    #[inline(always)]
    pub fn imm_u8_c(self) -> u8 {
        (self.0 >> 24) as u8
    }

    /// Bits 16-31: sign-extended i16 field.
    #[inline(always)]
    pub fn imm_i16_hi(self) -> i16 {
        (self.0 >> 16) as i16
    }

    /// Bits 8-23: u16 field.
    #[inline(always)]
    pub fn imm_u16_lo(self) -> u16 {
        (self.0 >> 8) as u16
    }

    /// For LocalGetI32/etc: byte offset from fp (bits 8..40).
    #[inline(always)]
    pub fn local_byte_offset(self) -> u32 {
        (self.0 >> 8) as u32
    }

    /// For LocalGetI32/etc: local index (bits 40..56).
    #[inline(always)]
    pub fn local_index(self) -> u16 {
        (self.0 >> 40) as u16
    }
}

impl InlineOp {
    /// Human-readable label for disassembly output.
    ///
    /// Uses `OpCode::wasm_name()` for the base name and appends
    /// decoded immediates via the appropriate accessor methods.
    pub fn display_label(self) -> String {
        let op = self.opcode();
        match op {
            OpCode::DataStream | OpCode::Nop => String::new(),
            OpCode::I32Const => format!("{} {}", op.wasm_name(), self.immediate_i32()),
            OpCode::I64Const => format!("{} {}", op.wasm_name(), self.immediate_i32()),
            OpCode::LocalGetI32
            | OpCode::LocalGetI64
            | OpCode::LocalSetI32
            | OpCode::LocalSetI64
            | OpCode::LocalTeeI32
            | OpCode::LocalTeeI64 => {
                format!("{} {}", op.wasm_name(), self.local_index())
            }
            OpCode::GlobalGet | OpCode::GlobalSet => {
                format!("{} {}", op.wasm_name(), self.immediate_u32())
            }
            OpCode::Call => format!("{} {}", op.wasm_name(), self.immediate_u32()),
            OpCode::Br | OpCode::BrIf => {
                format!("{} {}", op.wasm_name(), self.immediate_u32())
            }
            OpCode::Block | OpCode::Loop | OpCode::Else | OpCode::End => op.wasm_name().into(),
            OpCode::If => op.wasm_name().into(),
            _ => op.wasm_name().into(),
        }
    }
}

impl std::fmt::Display for InlineOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.display_label())
    }
}

impl std::fmt::Debug for InlineOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}(0x{:06x})", self.opcode(), self.immediate_u32())
    }
}

// --- Packing helpers ---

pub(crate) const IMM24_MAX: i32 = (1 << 23) - 1;
pub(crate) const IMM24_MIN: i32 = -(1 << 23);
pub(crate) const IMM24_MASK: u32 = 0x00FF_FFFF;

/// Pack an opcode with no immediate.
pub fn pack(opcode: OpCode) -> InlineOp {
    InlineOp(opcode as u64)
}

/// Pack an opcode with a signed 24-bit immediate.
pub fn pack_imm(opcode: OpCode, imm: i32) -> InlineOp {
    debug_assert!(imm >= IMM24_MIN && imm <= IMM24_MAX);
    InlineOp((((imm as u32) & IMM24_MASK) as u64) << 8 | (opcode as u64))
}

/// Pack an opcode with an unsigned 24-bit immediate.
pub fn pack_imm_u(opcode: OpCode, imm: u32) -> InlineOp {
    debug_assert!(imm <= IMM24_MASK);
    InlineOp(((imm as u64) << 8) | (opcode as u64))
}

/// Pack a typed local access: byte_offset in bits[8..40], local_index in bits[40..56].
pub fn pack_local(opcode: OpCode, byte_offset: u32, local_index: u16) -> InlineOp {
    InlineOp((opcode as u64) | ((byte_offset as u64) << 8) | ((local_index as u64) << 40))
}

/// Pack opcode + u8 in bits[8..16] + i16 in bits[16..32].
pub fn pack_u8_i16(opcode: OpCode, a: u8, val: i16) -> InlineOp {
    InlineOp((opcode as u64) | ((a as u64) << 8) | (((val as u16) as u64) << 16))
}

/// Pack opcode + u16 in bits[8..24] + u8 in bits[24..32].
pub fn pack_u16_u8(opcode: OpCode, a: u16, b: u8) -> InlineOp {
    InlineOp((opcode as u64) | ((a as u64) << 8) | ((b as u64) << 24))
}

/// Pack opcode + u8 in bits[8..16] + u8 in bits[16..24].
pub fn pack_two_u8(opcode: OpCode, a: u8, b: u8) -> InlineOp {
    InlineOp((opcode as u64) | ((a as u64) << 8) | ((b as u64) << 16))
}

/// Pack opcode + three u8 fields in bits[8..16], [16..24], [24..32].
pub fn pack_three_u8(opcode: OpCode, a: u8, b: u8, c: u8) -> InlineOp {
    InlineOp((opcode as u64) | ((a as u64) << 8) | ((b as u64) << 16) | ((c as u64) << 24))
}

pub(crate) fn fits_imm24(val: i64) -> bool {
    val >= IMM24_MIN as i64 && val <= IMM24_MAX as i64
}

pub(crate) fn fits_imm24_unsigned(val: u64) -> bool {
    val <= IMM24_MASK as u64
}

/// Wasm instruction opcodes decoded into a compact u8 discriminant.
///
/// These map 1:1 to wasm instructions. Superinstructions (fused
/// sequences) are engine-specific and not included here.
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum OpCode {
    // --- Data stream (opcode = 0) ---
    DataStream = 0,

    // --- No-immediate operations ---
    Nop,
    Unreachable,
    Return,

    // --- i32 arithmetic (no immediate) ---
    I32Add,
    I32Sub,

    // --- i32 comparison / test (no immediate) ---
    I32Eqz,
    I32LeS,

    // --- i32 arithmetic ---
    I32Mul,
    I32DivS,
    I32DivU,
    I32RemS,
    I32RemU,
    // --- i32 bitwise ---
    I32And,
    I32Or,
    I32Xor,
    I32Shl,
    I32ShrS,
    I32ShrU,
    I32Rotl,
    I32Rotr,
    // --- i32 comparison ---
    I32Eq,
    I32Ne,
    I32LtS,
    I32LtU,
    I32GtS,
    I32GtU,
    I32LeU,
    I32GeS,
    I32GeU,
    // --- i32 unary ---
    I32Clz,
    I32Ctz,
    I32Popcnt,
    // --- i32 conversion ---
    I32WrapI64,
    I32Extend8S,
    I32Extend16S,
    // --- i32 truncation from floats (trapping) ---
    I32TruncF32S,
    I32TruncF32U,
    I32TruncF64S,
    I32TruncF64U,
    // --- i32 truncation from floats (saturating) ---
    I32TruncSatF32S,
    I32TruncSatF32U,
    I32TruncSatF64S,
    I32TruncSatF64U,
    // --- i32 reinterpret ---
    I32ReinterpretF32,
    // --- i64 arithmetic ---
    I64Add,
    I64Sub,
    I64Mul,
    I64DivS,
    I64DivU,
    I64RemS,
    I64RemU,
    // --- i64 bitwise ---
    I64And,
    I64Or,
    I64Xor,
    I64Shl,
    I64ShrS,
    I64ShrU,
    I64Rotl,
    I64Rotr,
    // --- i64 comparison ---
    I64Eqz,
    I64Eq,
    I64Ne,
    I64LtS,
    I64LtU,
    I64GtS,
    I64GtU,
    I64LeS,
    I64LeU,
    I64GeS,
    I64GeU,
    // --- i64 unary ---
    I64Clz,
    I64Ctz,
    I64Popcnt,
    // --- i64 conversion ---
    I64ExtendI32S,
    I64ExtendI32U,
    I64Extend8S,
    I64Extend16S,
    I64Extend32S,
    // --- i64 truncation from floats (trapping) ---
    I64TruncF32S,
    I64TruncF32U,
    I64TruncF64S,
    I64TruncF64U,
    // --- i64 truncation from floats (saturating) ---
    I64TruncSatF32S,
    I64TruncSatF32U,
    I64TruncSatF64S,
    I64TruncSatF64U,
    // --- i64 reinterpret ---
    I64ReinterpretF64,

    // --- f32 arithmetic (binary) ---
    F32Add,
    F32Sub,
    F32Mul,
    F32Div,
    F32Min,
    F32Max,
    F32Copysign,
    // --- f32 arithmetic (unary) ---
    F32Abs,
    F32Neg,
    F32Sqrt,
    F32Ceil,
    F32Floor,
    F32Trunc,
    F32Nearest,
    // --- f32 comparison ---
    F32Eq,
    F32Ne,
    F32Lt,
    F32Gt,
    F32Le,
    F32Ge,
    // --- f32 conversion ---
    F32ConvertI32S,
    F32ConvertI32U,
    F32ConvertI64S,
    F32ConvertI64U,
    F32DemoteF64,
    F32ReinterpretI32,

    // --- f64 arithmetic (binary) ---
    F64Add,
    F64Sub,
    F64Mul,
    F64Div,
    F64Min,
    F64Max,
    F64Copysign,
    // --- f64 arithmetic (unary) ---
    F64Abs,
    F64Neg,
    F64Sqrt,
    F64Ceil,
    F64Floor,
    F64Trunc,
    F64Nearest,
    // --- f64 comparison ---
    F64Eq,
    F64Ne,
    F64Lt,
    F64Gt,
    F64Le,
    F64Ge,
    // --- f64 conversion ---
    F64ConvertI32S,
    F64ConvertI32U,
    F64ConvertI64S,
    F64ConvertI64U,
    F64PromoteF32,
    F64ReinterpretI64,

    // --- f32/f64 constants ---
    F32Const,
    F64Const,

    // --- Stack manipulation ---
    Drop,
    Select,

    // --- Reference operations ---
    RefNull,

    // --- Operations with immediates ---
    I32Const,
    I64Const,

    /// Type-specialized local access. Immediate = byte offset from fp.
    LocalGetI32,
    LocalSetI32,
    LocalTeeI32,
    LocalGetI64,
    LocalSetI64,
    LocalTeeI64,

    GlobalGet,
    GlobalSet,

    Call,

    Block,
    Loop,
    If,
    Else,
    End,
    Br,
    BrIf,
}

impl OpCode {
    /// Fuel cost for this opcode. Most ops cost 1. Structural ops that
    /// don't produce work (Nop, Block, Loop, Else, End) cost 0.
    /// Comparisons folded into branches (I32Eqz, I32LeS) cost 0.
    /// If and BrIf cost 2 (branch + condition check).
    pub fn fuel_cost(self) -> u32 {
        match self {
            OpCode::Nop
            | OpCode::DataStream
            | OpCode::Block
            | OpCode::Else
            | OpCode::End
            | OpCode::I32Eqz
            | OpCode::I32LeS => 0,
            OpCode::If | OpCode::BrIf => 2,
            OpCode::Call => 4,
            OpCode::Loop => 1,
            _ => 1,
        }
    }
}
