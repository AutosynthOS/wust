use wasmparser::{BlockType, FunctionBody, Operator};
use wasmparser::types::TypesRef;
#[cfg(test)]
mod tests;

/// A parsed function body, pre-decoded from raw wasm bytes.
#[derive(Debug, Clone, Default)]
pub(crate) struct ParsedBody {
    /// Op table: one entry per instruction (8 bytes each).
    pub(crate) ops: Vec<InlineOp>,

    /// Data stream for instructions that don't fit inline.
    pub(crate) data: Vec<u8>,

    /// Block metadata, indexed by block index.
    pub(crate) blocks: Vec<Block>,
}

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
pub(crate) struct InlineOp(u64);

impl InlineOp {
    /// Read the opcode byte as an `OpCode` reference via pointer cast.
    ///
    /// # Safety
    /// On little-endian, byte 0 of the u64 is the opcode. We only
    /// construct InlineOp from valid OpCode variants during parsing,
    /// so this is always a valid discriminant.
    #[inline(always)]
    pub(crate) fn opcode(&self) -> OpCode {
        // SAFETY: byte 0 of the u64 holds a valid OpCode discriminant
        // (we only write valid opcodes in pack/pack_imm/pack_imm_u).
        unsafe { *(&self.0 as *const u64 as *const OpCode) }
    }

    /// Read the immediate as a u32 (lower 24 bits of the immediate field).
    #[inline(always)]
    pub(crate) fn immediate_u32(self) -> u32 {
        (self.0 >> 8) as u32
    }

    /// Raw u64 value (for debugging/dump).
    pub fn raw(self) -> u64 {
        self.0
    }

    /// Bits 8-15: first u8 field.
    #[inline(always)]
    pub(crate) fn imm_u8_a(self) -> u8 {
        (self.0 >> 8) as u8
    }

    /// Bits 16-23: second u8 field.
    #[inline(always)]
    pub(crate) fn imm_u8_b(self) -> u8 {
        (self.0 >> 16) as u8
    }

    /// Bits 24-31: third u8 field.
    #[inline(always)]
    pub(crate) fn imm_u8_c(self) -> u8 {
        (self.0 >> 24) as u8
    }

    /// Bits 16-31: sign-extended i16 field.
    #[inline(always)]
    pub(crate) fn imm_i16_hi(self) -> i16 {
        (self.0 >> 16) as i16
    }

    /// Bits 8-23: u16 field.
    #[inline(always)]
    pub(crate) fn imm_u16_lo(self) -> u16 {
        (self.0 >> 8) as u16
    }
}

impl InlineOp {
    /// Format this parsed op as a human-readable expression.
    ///
    /// Superinstructions are shown as nested expressions:
    /// `sub(local.get 0, 1)`, `le_s(local.get 0, 1)`, etc.
    /// Structural ops (block, end, etc.) return empty strings.
    pub(crate) fn display_label(self) -> String {
        let imm = self.immediate_u32();
        match self.opcode() {
            OpCode::DataStream | OpCode::Nop => String::new(),
            OpCode::Unreachable => "unreachable".into(),
            OpCode::Return => "return".into(),
            OpCode::I32Add => "i32.add".into(),
            OpCode::I32Sub => "i32.sub".into(),
            OpCode::I32Eqz => "i32.eqz".into(),
            OpCode::I32LeS => "i32.le_s".into(),
            OpCode::I32Mul => "i32.mul".into(),
            OpCode::I32DivS => "i32.div_s".into(),
            OpCode::I32DivU => "i32.div_u".into(),
            OpCode::I32RemS => "i32.rem_s".into(),
            OpCode::I32RemU => "i32.rem_u".into(),
            OpCode::I32And => "i32.and".into(),
            OpCode::I32Or => "i32.or".into(),
            OpCode::I32Xor => "i32.xor".into(),
            OpCode::I32Shl => "i32.shl".into(),
            OpCode::I32ShrS => "i32.shr_s".into(),
            OpCode::I32ShrU => "i32.shr_u".into(),
            OpCode::I32Rotl => "i32.rotl".into(),
            OpCode::I32Rotr => "i32.rotr".into(),
            OpCode::I32Eq => "i32.eq".into(),
            OpCode::I32Ne => "i32.ne".into(),
            OpCode::I32LtS => "i32.lt_s".into(),
            OpCode::I32LtU => "i32.lt_u".into(),
            OpCode::I32GtS => "i32.gt_s".into(),
            OpCode::I32GtU => "i32.gt_u".into(),
            OpCode::I32LeU => "i32.le_u".into(),
            OpCode::I32GeS => "i32.ge_s".into(),
            OpCode::I32GeU => "i32.ge_u".into(),
            OpCode::I32Clz => "i32.clz".into(),
            OpCode::I32Ctz => "i32.ctz".into(),
            OpCode::I32Popcnt => "i32.popcnt".into(),
            OpCode::I32WrapI64 => "i32.wrap_i64".into(),
            OpCode::I32Extend8S => "i32.extend8_s".into(),
            OpCode::I32Extend16S => "i32.extend16_s".into(),
            OpCode::I32TruncF32S => "i32.trunc_f32_s".into(),
            OpCode::I32TruncF32U => "i32.trunc_f32_u".into(),
            OpCode::I32TruncF64S => "i32.trunc_f64_s".into(),
            OpCode::I32TruncF64U => "i32.trunc_f64_u".into(),
            OpCode::I32TruncSatF32S => "i32.trunc_sat_f32_s".into(),
            OpCode::I32TruncSatF32U => "i32.trunc_sat_f32_u".into(),
            OpCode::I32TruncSatF64S => "i32.trunc_sat_f64_s".into(),
            OpCode::I32TruncSatF64U => "i32.trunc_sat_f64_u".into(),
            OpCode::I32ReinterpretF32 => "i32.reinterpret_f32".into(),
            OpCode::I64Add => "i64.add".into(),
            OpCode::I64Sub => "i64.sub".into(),
            OpCode::I64Mul => "i64.mul".into(),
            OpCode::I64DivS => "i64.div_s".into(),
            OpCode::I64DivU => "i64.div_u".into(),
            OpCode::I64RemS => "i64.rem_s".into(),
            OpCode::I64RemU => "i64.rem_u".into(),
            OpCode::I64And => "i64.and".into(),
            OpCode::I64Or => "i64.or".into(),
            OpCode::I64Xor => "i64.xor".into(),
            OpCode::I64Shl => "i64.shl".into(),
            OpCode::I64ShrS => "i64.shr_s".into(),
            OpCode::I64ShrU => "i64.shr_u".into(),
            OpCode::I64Rotl => "i64.rotl".into(),
            OpCode::I64Rotr => "i64.rotr".into(),
            OpCode::I64Eqz => "i64.eqz".into(),
            OpCode::I64Eq => "i64.eq".into(),
            OpCode::I64Ne => "i64.ne".into(),
            OpCode::I64LtS => "i64.lt_s".into(),
            OpCode::I64LtU => "i64.lt_u".into(),
            OpCode::I64GtS => "i64.gt_s".into(),
            OpCode::I64GtU => "i64.gt_u".into(),
            OpCode::I64LeS => "i64.le_s".into(),
            OpCode::I64LeU => "i64.le_u".into(),
            OpCode::I64GeS => "i64.ge_s".into(),
            OpCode::I64GeU => "i64.ge_u".into(),
            OpCode::I64Clz => "i64.clz".into(),
            OpCode::I64Ctz => "i64.ctz".into(),
            OpCode::I64Popcnt => "i64.popcnt".into(),
            OpCode::I64ExtendI32S => "i64.extend_i32_s".into(),
            OpCode::I64ExtendI32U => "i64.extend_i32_u".into(),
            OpCode::I64Extend8S => "i64.extend8_s".into(),
            OpCode::I64Extend16S => "i64.extend16_s".into(),
            OpCode::I64Extend32S => "i64.extend32_s".into(),
            OpCode::I64TruncF32S => "i64.trunc_f32_s".into(),
            OpCode::I64TruncF32U => "i64.trunc_f32_u".into(),
            OpCode::I64TruncF64S => "i64.trunc_f64_s".into(),
            OpCode::I64TruncF64U => "i64.trunc_f64_u".into(),
            OpCode::I64TruncSatF32S => "i64.trunc_sat_f32_s".into(),
            OpCode::I64TruncSatF32U => "i64.trunc_sat_f32_u".into(),
            OpCode::I64TruncSatF64S => "i64.trunc_sat_f64_s".into(),
            OpCode::I64TruncSatF64U => "i64.trunc_sat_f64_u".into(),
            OpCode::I64ReinterpretF64 => "i64.reinterpret_f64".into(),
            OpCode::F32Add => "f32.add".into(),
            OpCode::F32Sub => "f32.sub".into(),
            OpCode::F32Mul => "f32.mul".into(),
            OpCode::F32Div => "f32.div".into(),
            OpCode::F32Min => "f32.min".into(),
            OpCode::F32Max => "f32.max".into(),
            OpCode::F32Copysign => "f32.copysign".into(),
            OpCode::F32Abs => "f32.abs".into(),
            OpCode::F32Neg => "f32.neg".into(),
            OpCode::F32Sqrt => "f32.sqrt".into(),
            OpCode::F32Ceil => "f32.ceil".into(),
            OpCode::F32Floor => "f32.floor".into(),
            OpCode::F32Trunc => "f32.trunc".into(),
            OpCode::F32Nearest => "f32.nearest".into(),
            OpCode::F32Eq => "f32.eq".into(),
            OpCode::F32Ne => "f32.ne".into(),
            OpCode::F32Lt => "f32.lt".into(),
            OpCode::F32Gt => "f32.gt".into(),
            OpCode::F32Le => "f32.le".into(),
            OpCode::F32Ge => "f32.ge".into(),
            OpCode::F32ConvertI32S => "f32.convert_i32_s".into(),
            OpCode::F32ConvertI32U => "f32.convert_i32_u".into(),
            OpCode::F32ConvertI64S => "f32.convert_i64_s".into(),
            OpCode::F32ConvertI64U => "f32.convert_i64_u".into(),
            OpCode::F32DemoteF64 => "f32.demote_f64".into(),
            OpCode::F32ReinterpretI32 => "f32.reinterpret_i32".into(),
            OpCode::F64Add => "f64.add".into(),
            OpCode::F64Sub => "f64.sub".into(),
            OpCode::F64Mul => "f64.mul".into(),
            OpCode::F64Div => "f64.div".into(),
            OpCode::F64Min => "f64.min".into(),
            OpCode::F64Max => "f64.max".into(),
            OpCode::F64Copysign => "f64.copysign".into(),
            OpCode::F64Abs => "f64.abs".into(),
            OpCode::F64Neg => "f64.neg".into(),
            OpCode::F64Sqrt => "f64.sqrt".into(),
            OpCode::F64Ceil => "f64.ceil".into(),
            OpCode::F64Floor => "f64.floor".into(),
            OpCode::F64Trunc => "f64.trunc".into(),
            OpCode::F64Nearest => "f64.nearest".into(),
            OpCode::F64Eq => "f64.eq".into(),
            OpCode::F64Ne => "f64.ne".into(),
            OpCode::F64Lt => "f64.lt".into(),
            OpCode::F64Gt => "f64.gt".into(),
            OpCode::F64Le => "f64.le".into(),
            OpCode::F64Ge => "f64.ge".into(),
            OpCode::F64ConvertI32S => "f64.convert_i32_s".into(),
            OpCode::F64ConvertI32U => "f64.convert_i32_u".into(),
            OpCode::F64ConvertI64S => "f64.convert_i64_s".into(),
            OpCode::F64ConvertI64U => "f64.convert_i64_u".into(),
            OpCode::F64PromoteF32 => "f64.promote_f32".into(),
            OpCode::F64ReinterpretI64 => "f64.reinterpret_i64".into(),
            OpCode::F32Const => "f32.const".into(),
            OpCode::F64Const => "f64.const".into(),
            OpCode::Drop => "drop".into(),
            OpCode::Select => "select".into(),
            OpCode::RefNull => "ref.null".into(),
            OpCode::I32Const => {
                let val = (imm as i32) << 8 >> 8;
                format!("i32.const {val}")
            }
            OpCode::I64Const => {
                let val = (imm as i32) << 8 >> 8;
                format!("i64.const {val}")
            }
            OpCode::LocalGet => format!("local.get {imm}"),
            OpCode::LocalSet => format!("local.set {imm}"),
            OpCode::LocalTee => format!("local.tee {imm}"),
            OpCode::GlobalGet => format!("global.get {imm}"),
            OpCode::GlobalSet => format!("global.set {imm}"),
            OpCode::Call => format!("call {imm}"),
            OpCode::Block | OpCode::Loop | OpCode::Else | OpCode::End => String::new(),
            OpCode::If => "if".into(),
            OpCode::Br => format!("br {imm}"),
            OpCode::BrIf => format!("br_if {imm}"),
            OpCode::LocalGetI32ConstSub => {
                let local = self.imm_u8_a();
                let konst = self.imm_i16_hi();
                format!("sub(local.get {local}, {konst})")
            }
            OpCode::LocalGetI32ConstAdd => {
                let local = self.imm_u8_a();
                let konst = self.imm_i16_hi();
                format!("add(local.get {local}, {konst})")
            }
            OpCode::CallLocalSet => {
                let func = self.imm_u16_lo();
                let local = self.imm_u8_c();
                format!("call {func} -> local.set {local}")
            }
            OpCode::LocalGetLocalGetAdd => {
                let a = self.imm_u8_a();
                let b = self.imm_u8_b();
                format!("add(local.get {a}, local.get {b})")
            }
            OpCode::LocalGetReturn => {
                let local = self.imm_u8_a();
                format!("return local.get {local}")
            }
            OpCode::LocalGetI32ConstLeSIf => {
                let local = self.imm_u8_a();
                let konst = self.imm_u8_b() as i8;
                format!("if le_s(local.get {local}, {konst})")
            }
            OpCode::LocalGetI32EqzIf => {
                let local = self.imm_u8_a();
                format!("if eqz(local.get {local})")
            }
        }
    }
}

impl std::fmt::Debug for InlineOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("InlineOp")
            .field("opcode", &self.opcode())
            .field("immediate", &self.immediate_u32())
            .finish()
    }
}

/// Flat opcode — 8 bits, up to 256 instruction types.
///
/// Variant 0 (`DataStream`) means the immediate is a data stream
/// offset. All other variants are directly executable opcodes.
/// `#[repr(u8)]` ensures each variant is a single byte.
#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(u8)]
pub(crate) enum OpCode {
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
    RefNull, // push null ref (no immediate)

    // --- Operations with immediates ---
    I32Const, // imm = sign-extended 24-bit value
    I64Const, // imm = sign-extended 24-bit value

    LocalGet, // imm = local index
    LocalSet, // imm = local index
    LocalTee, // imm = local index

    GlobalGet, // imm = global index
    GlobalSet, // imm = global index

    Call, // imm = function index

    Block, // imm = block index
    Loop,  // imm = block index
    If,    // imm = block index
    Else,  // imm = block index
    End,   // imm = block index
    Br,    // imm = relative block depth
    BrIf,  // imm = relative block depth

    // --- Superinstructions (fused sequences) ---
    LocalGetI32ConstSub,   // local(8) + const_i16(16)
    LocalGetI32ConstAdd,   // local(8) + const_i16(16)
    CallLocalSet,          // func(16) + local(8)
    LocalGetLocalGetAdd,   // localA(8) + localB(8)
    LocalGetReturn,        // local(8)
    LocalGetI32ConstLeSIf, // local(8) + const_i8(8) + block(8)
    LocalGetI32EqzIf,      // local(8) + block(8)
}

impl OpCode {
    /// Fuel cost for this opcode. Zero means no fuel check is emitted
    /// after this opcode's IR group.
    ///
    /// Comparisons (I32Eqz, I32LeS) cost 0 because their IR (Cmp)
    /// must stay adjacent to the following branch (BrIfZero) for
    /// fusion. The branch opcode (If, BrIf) charges for both.
    pub(crate) fn fuel_cost(self) -> u32 {
        match self {
            // Structural — no work.
            OpCode::Nop | OpCode::Block | OpCode::Loop | OpCode::Else | OpCode::End => 0,
            // Comparisons — cost folded into the following branch.
            OpCode::I32Eqz | OpCode::I32LeS => 0,
            // Branches charge for the preceding comparison too.
            OpCode::If | OpCode::BrIf => 2,
            // Superinstructions cost the number of fused wasm opcodes.
            OpCode::LocalGetI32ConstSub
            | OpCode::LocalGetI32ConstAdd
            | OpCode::LocalGetLocalGetAdd => 3,
            OpCode::CallLocalSet => 2,
            OpCode::LocalGetReturn => 2,
            OpCode::LocalGetI32ConstLeSIf => 4,
            OpCode::LocalGetI32EqzIf => 3,
            // Everything else: 1 fuel per wasm opcode.
            _ => 1,
        }
    }
}

/// Metadata for a block/loop/if/function, resolved at parse time.
#[derive(Debug, Clone)]
pub(crate) struct Block {
    pub(crate) kind: BlockKind,
    /// PC of the block opener (block/loop/if instruction).
    pub(crate) start_pc: u32,
    /// PC of the `end` instruction (patched when `end` is parsed).
    pub(crate) end_pc: u32,
    /// PC of the `else` instruction (only for `If`, 0 if no else).
    pub(crate) else_pc: u32,
    /// Number of result values this block produces.
    pub(crate) result_count: u32,
    /// Number of parameter values this block consumes (non-zero only for multi-value).
    pub(crate) param_count: u32,
    /// Operand stack height (bytes, relative to locals base) at block entry.
    /// Precomputed at parse time so the interpreter never tracks block frames.
    pub(crate) entry_sp_offset: u32,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum BlockKind {
    /// Implicit function-level block.
    Function,
    Block,
    Loop,
    If,
}

const IMM24_MAX: i32 = (1 << 23) - 1;
const IMM24_MIN: i32 = -(1 << 23);
const IMM24_MASK: u32 = 0x00FF_FFFF;

/// Pack an opcode with no immediate.
fn pack(opcode: OpCode) -> InlineOp {
    InlineOp(opcode as u64)
}

/// Pack an opcode with a signed 24-bit immediate.
fn pack_imm(opcode: OpCode, imm: i32) -> InlineOp {
    debug_assert!(imm >= IMM24_MIN && imm <= IMM24_MAX);
    InlineOp((((imm as u32) & IMM24_MASK) as u64) << 8 | (opcode as u64))
}

/// Pack an opcode with an unsigned 24-bit immediate.
fn pack_imm_u(opcode: OpCode, imm: u32) -> InlineOp {
    debug_assert!(imm <= IMM24_MASK);
    InlineOp(((imm as u64) << 8) | (opcode as u64))
}

/// Pack opcode + u8 in bits[8..16] + i16 in bits[16..32].
fn pack_u8_i16(opcode: OpCode, a: u8, val: i16) -> InlineOp {
    InlineOp((opcode as u64) | ((a as u64) << 8) | (((val as u16) as u64) << 16))
}

/// Pack opcode + u16 in bits[8..24] + u8 in bits[24..32].
fn pack_u16_u8(opcode: OpCode, a: u16, b: u8) -> InlineOp {
    InlineOp((opcode as u64) | ((a as u64) << 8) | ((b as u64) << 24))
}

/// Pack opcode + u8 in bits[8..16] + u8 in bits[16..24].
fn pack_two_u8(opcode: OpCode, a: u8, b: u8) -> InlineOp {
    InlineOp((opcode as u64) | ((a as u64) << 8) | ((b as u64) << 16))
}

/// Pack opcode + three u8 fields in bits[8..16], [16..24], [24..32].
fn pack_three_u8(opcode: OpCode, a: u8, b: u8, c: u8) -> InlineOp {
    InlineOp((opcode as u64) | ((a as u64) << 8) | ((b as u64) << 16) | ((c as u64) << 24))
}

/// Resolve a wasm `BlockType` to (result_count, param_count).
fn resolve_block_type(bt: BlockType, types: &TypesRef) -> (u32, u32) {
    match bt {
        BlockType::Empty => (0, 0),
        BlockType::Type(_) => (1, 0),
        BlockType::FuncType(idx) => {
            let core_type_id = types.core_type_at_in_module(idx);
            let func_type = types[core_type_id].unwrap_func();
            (func_type.results().len() as u32, func_type.params().len() as u32)
        }
    }
}

fn fits_imm24(val: i64) -> bool {
    val >= IMM24_MIN as i64 && val <= IMM24_MAX as i64
}

fn fits_imm24_unsigned(val: u64) -> bool {
    val <= IMM24_MASK as u64
}

impl ParsedBody {
    /// Parse raw wasm function body bytes into a pre-decoded body.
    pub(crate) fn parse(reader: &FunctionBody, types: &TypesRef) -> Result<Self, anyhow::Error> {
        let mut body = Self::default();

        // Operand stack height in bytes, relative to locals base.
        // Tracked at parse time so blocks can record their entry_sp_offset.
        let mut stack_height: u32 = 0;

        // Implicit function-level block (index 0).
        // Result count is patched later in build() since we don't have
        // access to the function signature here.
        let func_block_idx = body.open_block(BlockKind::Function, 0, 0, stack_height);

        let ops_reader = reader.get_operators_reader()?;
        // Track open block indices so `end` can find the right one.
        let mut block_stack: Vec<u32> = vec![func_block_idx];

        for op in ops_reader {
            body.parse_op(op?, &mut block_stack, types, &mut stack_height)?;
        }
        body.fuse();
        Ok(body)
    }

    /// Allocate a new block entry, returning its index.
    fn open_block(&mut self, kind: BlockKind, result_count: u32, param_count: u32, entry_sp_offset: u32) -> u32 {
        let idx = self.blocks.len() as u32;
        self.blocks.push(Block {
            kind,
            start_pc: self.ops.len() as u32,
            end_pc: 0,
            else_pc: 0,
            result_count,
            param_count,
            entry_sp_offset,
        });
        idx
    }

    fn parse_op(&mut self, op: Operator, block_stack: &mut Vec<u32>, types: &TypesRef, _stack_height: &mut u32) -> Result<(), anyhow::Error> {
        match op {
            // No-immediate ops
            Operator::Nop => self.ops.push(pack(OpCode::Nop)),
            Operator::Unreachable => self.ops.push(pack(OpCode::Unreachable)),
            Operator::Return => self.ops.push(pack(OpCode::Return)),

            // Block control flow
            Operator::Block { blockty } => {
                let (rc, pc) = resolve_block_type(blockty, types);
                let idx = self.open_block(BlockKind::Block, rc, pc, 0);
                block_stack.push(idx);
                self.ops.push(pack_imm_u(OpCode::Block, idx));
            }
            Operator::Loop { blockty } => {
                let (rc, pc) = resolve_block_type(blockty, types);
                let idx = self.open_block(BlockKind::Loop, rc, pc, 0);
                block_stack.push(idx);
                self.ops.push(pack_imm_u(OpCode::Loop, idx));
            }
            Operator::If { blockty } => {
                let (rc, pc) = resolve_block_type(blockty, types);
                let idx = self.open_block(BlockKind::If, rc, pc, 0);
                block_stack.push(idx);
                self.ops.push(pack_imm_u(OpCode::If, idx));
            }
            Operator::Else => {
                let &idx = block_stack
                    .last()
                    .ok_or_else(|| anyhow::anyhow!("else without open block"))?;
                self.blocks[idx as usize].else_pc = self.ops.len() as u32;
                self.ops.push(pack_imm_u(OpCode::Else, idx));
            }
            Operator::End => {
                let idx = block_stack
                    .pop()
                    .ok_or_else(|| anyhow::anyhow!("end without open block"))?;
                self.blocks[idx as usize].end_pc = self.ops.len() as u32;
                self.ops.push(pack_imm_u(OpCode::End, idx));
            }

            // i32 arithmetic
            Operator::I32Add => self.ops.push(pack(OpCode::I32Add)),
            Operator::I32Sub => self.ops.push(pack(OpCode::I32Sub)),

            // i32 comparison / test
            Operator::I32Eqz => self.ops.push(pack(OpCode::I32Eqz)),
            Operator::I32LeS => self.ops.push(pack(OpCode::I32LeS)),

            // i32 arithmetic
            Operator::I32Mul => self.ops.push(pack(OpCode::I32Mul)),
            Operator::I32DivS => self.ops.push(pack(OpCode::I32DivS)),
            Operator::I32DivU => self.ops.push(pack(OpCode::I32DivU)),
            Operator::I32RemS => self.ops.push(pack(OpCode::I32RemS)),
            Operator::I32RemU => self.ops.push(pack(OpCode::I32RemU)),
            // i32 bitwise
            Operator::I32And => self.ops.push(pack(OpCode::I32And)),
            Operator::I32Or => self.ops.push(pack(OpCode::I32Or)),
            Operator::I32Xor => self.ops.push(pack(OpCode::I32Xor)),
            Operator::I32Shl => self.ops.push(pack(OpCode::I32Shl)),
            Operator::I32ShrS => self.ops.push(pack(OpCode::I32ShrS)),
            Operator::I32ShrU => self.ops.push(pack(OpCode::I32ShrU)),
            Operator::I32Rotl => self.ops.push(pack(OpCode::I32Rotl)),
            Operator::I32Rotr => self.ops.push(pack(OpCode::I32Rotr)),
            // i32 comparison
            Operator::I32Eq => self.ops.push(pack(OpCode::I32Eq)),
            Operator::I32Ne => self.ops.push(pack(OpCode::I32Ne)),
            Operator::I32LtS => self.ops.push(pack(OpCode::I32LtS)),
            Operator::I32LtU => self.ops.push(pack(OpCode::I32LtU)),
            Operator::I32GtS => self.ops.push(pack(OpCode::I32GtS)),
            Operator::I32GtU => self.ops.push(pack(OpCode::I32GtU)),
            Operator::I32LeU => self.ops.push(pack(OpCode::I32LeU)),
            Operator::I32GeS => self.ops.push(pack(OpCode::I32GeS)),
            Operator::I32GeU => self.ops.push(pack(OpCode::I32GeU)),
            // i32 unary
            Operator::I32Clz => self.ops.push(pack(OpCode::I32Clz)),
            Operator::I32Ctz => self.ops.push(pack(OpCode::I32Ctz)),
            Operator::I32Popcnt => self.ops.push(pack(OpCode::I32Popcnt)),
            // i32 conversion
            Operator::I32WrapI64 => self.ops.push(pack(OpCode::I32WrapI64)),
            Operator::I32Extend8S => self.ops.push(pack(OpCode::I32Extend8S)),
            Operator::I32Extend16S => self.ops.push(pack(OpCode::I32Extend16S)),
            // i32 truncation from floats (trapping)
            Operator::I32TruncF32S => self.ops.push(pack(OpCode::I32TruncF32S)),
            Operator::I32TruncF32U => self.ops.push(pack(OpCode::I32TruncF32U)),
            Operator::I32TruncF64S => self.ops.push(pack(OpCode::I32TruncF64S)),
            Operator::I32TruncF64U => self.ops.push(pack(OpCode::I32TruncF64U)),
            // i32 truncation from floats (saturating)
            Operator::I32TruncSatF32S => self.ops.push(pack(OpCode::I32TruncSatF32S)),
            Operator::I32TruncSatF32U => self.ops.push(pack(OpCode::I32TruncSatF32U)),
            Operator::I32TruncSatF64S => self.ops.push(pack(OpCode::I32TruncSatF64S)),
            Operator::I32TruncSatF64U => self.ops.push(pack(OpCode::I32TruncSatF64U)),
            // i32 reinterpret
            Operator::I32ReinterpretF32 => self.ops.push(pack(OpCode::I32ReinterpretF32)),
            // i64 arithmetic
            Operator::I64Add => self.ops.push(pack(OpCode::I64Add)),
            Operator::I64Sub => self.ops.push(pack(OpCode::I64Sub)),
            Operator::I64Mul => self.ops.push(pack(OpCode::I64Mul)),
            Operator::I64DivS => self.ops.push(pack(OpCode::I64DivS)),
            Operator::I64DivU => self.ops.push(pack(OpCode::I64DivU)),
            Operator::I64RemS => self.ops.push(pack(OpCode::I64RemS)),
            Operator::I64RemU => self.ops.push(pack(OpCode::I64RemU)),
            // i64 bitwise
            Operator::I64And => self.ops.push(pack(OpCode::I64And)),
            Operator::I64Or => self.ops.push(pack(OpCode::I64Or)),
            Operator::I64Xor => self.ops.push(pack(OpCode::I64Xor)),
            Operator::I64Shl => self.ops.push(pack(OpCode::I64Shl)),
            Operator::I64ShrS => self.ops.push(pack(OpCode::I64ShrS)),
            Operator::I64ShrU => self.ops.push(pack(OpCode::I64ShrU)),
            Operator::I64Rotl => self.ops.push(pack(OpCode::I64Rotl)),
            Operator::I64Rotr => self.ops.push(pack(OpCode::I64Rotr)),
            // i64 comparison
            Operator::I64Eqz => self.ops.push(pack(OpCode::I64Eqz)),
            Operator::I64Eq => self.ops.push(pack(OpCode::I64Eq)),
            Operator::I64Ne => self.ops.push(pack(OpCode::I64Ne)),
            Operator::I64LtS => self.ops.push(pack(OpCode::I64LtS)),
            Operator::I64LtU => self.ops.push(pack(OpCode::I64LtU)),
            Operator::I64GtS => self.ops.push(pack(OpCode::I64GtS)),
            Operator::I64GtU => self.ops.push(pack(OpCode::I64GtU)),
            Operator::I64LeS => self.ops.push(pack(OpCode::I64LeS)),
            Operator::I64LeU => self.ops.push(pack(OpCode::I64LeU)),
            Operator::I64GeS => self.ops.push(pack(OpCode::I64GeS)),
            Operator::I64GeU => self.ops.push(pack(OpCode::I64GeU)),
            // i64 unary
            Operator::I64Clz => self.ops.push(pack(OpCode::I64Clz)),
            Operator::I64Ctz => self.ops.push(pack(OpCode::I64Ctz)),
            Operator::I64Popcnt => self.ops.push(pack(OpCode::I64Popcnt)),
            // i64 conversion
            Operator::I64ExtendI32S => self.ops.push(pack(OpCode::I64ExtendI32S)),
            Operator::I64ExtendI32U => self.ops.push(pack(OpCode::I64ExtendI32U)),
            Operator::I64Extend8S => self.ops.push(pack(OpCode::I64Extend8S)),
            Operator::I64Extend16S => self.ops.push(pack(OpCode::I64Extend16S)),
            Operator::I64Extend32S => self.ops.push(pack(OpCode::I64Extend32S)),
            // i64 truncation from floats (trapping)
            Operator::I64TruncF32S => self.ops.push(pack(OpCode::I64TruncF32S)),
            Operator::I64TruncF32U => self.ops.push(pack(OpCode::I64TruncF32U)),
            Operator::I64TruncF64S => self.ops.push(pack(OpCode::I64TruncF64S)),
            Operator::I64TruncF64U => self.ops.push(pack(OpCode::I64TruncF64U)),
            // i64 truncation from floats (saturating)
            Operator::I64TruncSatF32S => self.ops.push(pack(OpCode::I64TruncSatF32S)),
            Operator::I64TruncSatF32U => self.ops.push(pack(OpCode::I64TruncSatF32U)),
            Operator::I64TruncSatF64S => self.ops.push(pack(OpCode::I64TruncSatF64S)),
            Operator::I64TruncSatF64U => self.ops.push(pack(OpCode::I64TruncSatF64U)),
            // i64 reinterpret
            Operator::I64ReinterpretF64 => self.ops.push(pack(OpCode::I64ReinterpretF64)),
            // f32 arithmetic
            Operator::F32Add => self.ops.push(pack(OpCode::F32Add)),
            Operator::F32Sub => self.ops.push(pack(OpCode::F32Sub)),
            Operator::F32Mul => self.ops.push(pack(OpCode::F32Mul)),
            Operator::F32Div => self.ops.push(pack(OpCode::F32Div)),
            Operator::F32Min => self.ops.push(pack(OpCode::F32Min)),
            Operator::F32Max => self.ops.push(pack(OpCode::F32Max)),
            Operator::F32Copysign => self.ops.push(pack(OpCode::F32Copysign)),
            // f32 unary
            Operator::F32Abs => self.ops.push(pack(OpCode::F32Abs)),
            Operator::F32Neg => self.ops.push(pack(OpCode::F32Neg)),
            Operator::F32Sqrt => self.ops.push(pack(OpCode::F32Sqrt)),
            Operator::F32Ceil => self.ops.push(pack(OpCode::F32Ceil)),
            Operator::F32Floor => self.ops.push(pack(OpCode::F32Floor)),
            Operator::F32Trunc => self.ops.push(pack(OpCode::F32Trunc)),
            Operator::F32Nearest => self.ops.push(pack(OpCode::F32Nearest)),
            // f32 comparison
            Operator::F32Eq => self.ops.push(pack(OpCode::F32Eq)),
            Operator::F32Ne => self.ops.push(pack(OpCode::F32Ne)),
            Operator::F32Lt => self.ops.push(pack(OpCode::F32Lt)),
            Operator::F32Gt => self.ops.push(pack(OpCode::F32Gt)),
            Operator::F32Le => self.ops.push(pack(OpCode::F32Le)),
            Operator::F32Ge => self.ops.push(pack(OpCode::F32Ge)),
            // f32 conversion
            Operator::F32ConvertI32S => self.ops.push(pack(OpCode::F32ConvertI32S)),
            Operator::F32ConvertI32U => self.ops.push(pack(OpCode::F32ConvertI32U)),
            Operator::F32ConvertI64S => self.ops.push(pack(OpCode::F32ConvertI64S)),
            Operator::F32ConvertI64U => self.ops.push(pack(OpCode::F32ConvertI64U)),
            Operator::F32DemoteF64 => self.ops.push(pack(OpCode::F32DemoteF64)),
            Operator::F32ReinterpretI32 => self.ops.push(pack(OpCode::F32ReinterpretI32)),
            // f64 arithmetic
            Operator::F64Add => self.ops.push(pack(OpCode::F64Add)),
            Operator::F64Sub => self.ops.push(pack(OpCode::F64Sub)),
            Operator::F64Mul => self.ops.push(pack(OpCode::F64Mul)),
            Operator::F64Div => self.ops.push(pack(OpCode::F64Div)),
            Operator::F64Min => self.ops.push(pack(OpCode::F64Min)),
            Operator::F64Max => self.ops.push(pack(OpCode::F64Max)),
            Operator::F64Copysign => self.ops.push(pack(OpCode::F64Copysign)),
            // f64 unary
            Operator::F64Abs => self.ops.push(pack(OpCode::F64Abs)),
            Operator::F64Neg => self.ops.push(pack(OpCode::F64Neg)),
            Operator::F64Sqrt => self.ops.push(pack(OpCode::F64Sqrt)),
            Operator::F64Ceil => self.ops.push(pack(OpCode::F64Ceil)),
            Operator::F64Floor => self.ops.push(pack(OpCode::F64Floor)),
            Operator::F64Trunc => self.ops.push(pack(OpCode::F64Trunc)),
            Operator::F64Nearest => self.ops.push(pack(OpCode::F64Nearest)),
            // f64 comparison
            Operator::F64Eq => self.ops.push(pack(OpCode::F64Eq)),
            Operator::F64Ne => self.ops.push(pack(OpCode::F64Ne)),
            Operator::F64Lt => self.ops.push(pack(OpCode::F64Lt)),
            Operator::F64Gt => self.ops.push(pack(OpCode::F64Gt)),
            Operator::F64Le => self.ops.push(pack(OpCode::F64Le)),
            Operator::F64Ge => self.ops.push(pack(OpCode::F64Ge)),
            // f64 conversion
            Operator::F64ConvertI32S => self.ops.push(pack(OpCode::F64ConvertI32S)),
            Operator::F64ConvertI32U => self.ops.push(pack(OpCode::F64ConvertI32U)),
            Operator::F64ConvertI64S => self.ops.push(pack(OpCode::F64ConvertI64S)),
            Operator::F64ConvertI64U => self.ops.push(pack(OpCode::F64ConvertI64U)),
            Operator::F64PromoteF32 => self.ops.push(pack(OpCode::F64PromoteF32)),
            Operator::F64ReinterpretI64 => self.ops.push(pack(OpCode::F64ReinterpretI64)),
            // f32/f64 constants (always spill to data stream)
            Operator::F32Const { value } => {
                self.emit_data(OpCode::F32Const, &value.bits().to_le_bytes());
            }
            Operator::F64Const { value } => {
                self.emit_data(OpCode::F64Const, &value.bits().to_le_bytes());
            }

            // Stack manipulation
            Operator::Drop => self.ops.push(pack(OpCode::Drop)),
            Operator::Select => self.ops.push(pack(OpCode::Select)),
            Operator::TypedSelect { .. } => self.ops.push(pack(OpCode::Select)),

            // References
            Operator::RefNull { .. } => self.ops.push(pack(OpCode::RefNull)),

            // Constants (signed immediate or data stream)
            Operator::I32Const { value } => {
                self.emit_signed(OpCode::I32Const, value as i64, &value.to_le_bytes());
            }
            Operator::I64Const { value } => {
                self.emit_signed(OpCode::I64Const, value, &value.to_le_bytes());
            }

            // Locals (unsigned immediate — index always fits)
            Operator::LocalGet { local_index } => {
                self.emit_unsigned(OpCode::LocalGet, local_index);
            }
            Operator::LocalSet { local_index } => {
                self.emit_unsigned(OpCode::LocalSet, local_index);
            }
            Operator::LocalTee { local_index } => {
                self.emit_unsigned(OpCode::LocalTee, local_index);
            }

            // Globals
            Operator::GlobalGet { global_index } => {
                self.emit_unsigned(OpCode::GlobalGet, global_index);
            }
            Operator::GlobalSet { global_index } => {
                self.emit_unsigned(OpCode::GlobalSet, global_index);
            }

            // Branches — resolve relative depth to block index.
            Operator::Br { relative_depth, .. } => {
                let block_idx = block_stack[block_stack.len() - 1 - relative_depth as usize];
                self.emit_unsigned(OpCode::Br, block_idx);
            }
            Operator::BrIf { relative_depth, .. } => {
                let block_idx = block_stack[block_stack.len() - 1 - relative_depth as usize];
                self.emit_unsigned(OpCode::BrIf, block_idx);
            }

            // Call
            Operator::Call { function_index } => {
                self.emit_unsigned(OpCode::Call, function_index);
            }

            // Unimplemented opcodes emit Unreachable so the interpreter
            // traps cleanly instead of silently corrupting the stack.
            _ => self.ops.push(pack(OpCode::Unreachable)),
        }
        Ok(())
    }

    /// Emit a signed immediate. Inline if it fits in 24 bits,
    /// otherwise spill to the data stream.
    fn emit_signed(&mut self, opcode: OpCode, value: i64, full_bytes: &[u8]) {
        if fits_imm24(value) {
            self.ops.push(pack_imm(opcode, value as i32));
        } else {
            self.emit_data(opcode, full_bytes);
        }
    }

    /// Emit an unsigned immediate. Inline if it fits in 24 bits,
    /// otherwise spill to the data stream.
    fn emit_unsigned(&mut self, opcode: OpCode, value: u32) {
        if fits_imm24_unsigned(value as u64) {
            self.ops.push(pack_imm_u(opcode, value));
        } else {
            self.emit_data(opcode, &value.to_le_bytes());
        }
    }

    /// Spill an instruction to the data stream.
    /// Stores: [opcode_byte, ...full_bytes] at the current data offset.
    fn emit_data(&mut self, opcode: OpCode, bytes: &[u8]) {
        let offset = self.data.len() as u32;
        debug_assert!(fits_imm24_unsigned(offset as u64), "data offset overflow");
        // The ops entry points to the data stream with opcode = DataStream.
        self.ops.push(pack_imm_u(OpCode::DataStream, offset));
        // In the data stream, store the real opcode + payload.
        self.data.push(opcode as u8);
        self.data.extend_from_slice(bytes);
    }

    /// Peephole fusion pass: replace common op sequences with
    /// superinstructions to reduce dispatch overhead.
    ///
    /// Builds a new ops vec, tracks old→new PC mapping, then remaps
    /// all block metadata (start_pc, end_pc, else_pc).
    fn fuse(&mut self) {
        let old_ops = &self.ops;
        let len = old_ops.len();
        let mut new_ops = Vec::with_capacity(len);
        // Map from old PC → new PC for block remapping.
        let mut pc_map: Vec<u32> = vec![0; len + 1];
        let mut i = 0;

        while i < len {
            pc_map[i] = new_ops.len() as u32;
            let fused = self.try_fuse_at(old_ops, i, len);
            if let Some((op, consumed)) = fused {
                new_ops.push(op);
                // Fill intermediate PCs to map to the same new PC.
                for j in 1..consumed {
                    pc_map[i + j] = pc_map[i];
                }
                i += consumed;
            } else {
                new_ops.push(old_ops[i]);
                i += 1;
            }
        }
        // Sentinel: end+1 maps correctly.
        pc_map[len] = new_ops.len() as u32;

        self.ops = new_ops;
        self.remap_blocks(&pc_map);
    }

    /// Try to fuse a sequence starting at `i`. Returns the fused op
    /// and how many original ops it consumed, or None if no fusion.
    fn try_fuse_at(&self, ops: &[InlineOp], i: usize, len: usize) -> Option<(InlineOp, usize)> {
        let remaining = len - i;

        // 4-op: LocalGet + I32Const + I32LeS + If
        if remaining >= 4 {
            let (o0, o1, o2, o3) = (ops[i], ops[i + 1], ops[i + 2], ops[i + 3]);
            if o0.opcode() == OpCode::LocalGet
                && o1.opcode() == OpCode::I32Const
                && o2.opcode() == OpCode::I32LeS
                && o3.opcode() == OpCode::If
            {
                let local = o0.immediate_u32();
                let konst = (o1.immediate_u32() as i32) << 8 >> 8;
                let block = o3.immediate_u32();
                if local < 256 && konst >= i8::MIN as i32 && konst <= i8::MAX as i32 && block < 256
                {
                    return Some((
                        pack_three_u8(
                            OpCode::LocalGetI32ConstLeSIf,
                            local as u8,
                            konst as u8,
                            block as u8,
                        ),
                        4,
                    ));
                }
            }
        }

        // 3-op fusions
        if remaining >= 3 {
            let (o0, o1, o2) = (ops[i], ops[i + 1], ops[i + 2]);

            // LocalGet + I32Const + I32Sub
            if o0.opcode() == OpCode::LocalGet
                && o1.opcode() == OpCode::I32Const
                && o2.opcode() == OpCode::I32Sub
            {
                let local = o0.immediate_u32();
                let konst = (o1.immediate_u32() as i32) << 8 >> 8;
                if local < 256 && konst >= i16::MIN as i32 && konst <= i16::MAX as i32 {
                    return Some((
                        pack_u8_i16(OpCode::LocalGetI32ConstSub, local as u8, konst as i16),
                        3,
                    ));
                }
            }

            // LocalGet + I32Const + I32Add
            if o0.opcode() == OpCode::LocalGet
                && o1.opcode() == OpCode::I32Const
                && o2.opcode() == OpCode::I32Add
            {
                let local = o0.immediate_u32();
                let konst = (o1.immediate_u32() as i32) << 8 >> 8;
                if local < 256 && konst >= i16::MIN as i32 && konst <= i16::MAX as i32 {
                    return Some((
                        pack_u8_i16(OpCode::LocalGetI32ConstAdd, local as u8, konst as i16),
                        3,
                    ));
                }
            }

            // LocalGet + I32Eqz + If
            if o0.opcode() == OpCode::LocalGet
                && o1.opcode() == OpCode::I32Eqz
                && o2.opcode() == OpCode::If
            {
                let local = o0.immediate_u32();
                let block = o2.immediate_u32();
                if local < 256 && block < 256 {
                    return Some((
                        pack_two_u8(OpCode::LocalGetI32EqzIf, local as u8, block as u8),
                        3,
                    ));
                }
            }

            // LocalGet + LocalGet + I32Add
            if o0.opcode() == OpCode::LocalGet
                && o1.opcode() == OpCode::LocalGet
                && o2.opcode() == OpCode::I32Add
            {
                let a = o0.immediate_u32();
                let b = o1.immediate_u32();
                if a < 256 && b < 256 {
                    return Some((
                        pack_two_u8(OpCode::LocalGetLocalGetAdd, a as u8, b as u8),
                        3,
                    ));
                }
            }
        }

        // 2-op fusions
        if remaining >= 2 {
            let (o0, o1) = (ops[i], ops[i + 1]);

            // Call + LocalSet
            if o0.opcode() == OpCode::Call && o1.opcode() == OpCode::LocalSet {
                let func = o0.immediate_u32();
                let local = o1.immediate_u32();
                if func < 65536 && local < 256 {
                    return Some((
                        pack_u16_u8(OpCode::CallLocalSet, func as u16, local as u8),
                        2,
                    ));
                }
            }

            // LocalGet + Return
            if o0.opcode() == OpCode::LocalGet && o1.opcode() == OpCode::Return {
                let local = o0.immediate_u32();
                if local < 256 {
                    return Some((pack_imm_u(OpCode::LocalGetReturn, local), 2));
                }
            }
        }

        None
    }

    /// Remap block start_pc, end_pc, else_pc using old→new PC mapping.
    fn remap_blocks(&mut self, pc_map: &[u32]) {
        for block in &mut self.blocks {
            block.start_pc = pc_map[block.start_pc as usize];
            block.end_pc = pc_map[block.end_pc as usize];
            if block.else_pc != 0 {
                block.else_pc = pc_map[block.else_pc as usize];
            }
        }
    }

    /// An empty body (for imported functions).
    pub(crate) fn empty() -> Self {
        // Emit Unreachable so that calling an imported (unlinked) function
        // produces a clean trap instead of reading from an empty ops slice.
        ParsedBody {
            ops: vec![pack(OpCode::Unreachable)],
            data: Vec::new(),
            blocks: Vec::new(),
        }
    }
}
