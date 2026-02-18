use wasmparser::FuncType;

use crate::runtime::instruction::{BlockType, Instruction};

/// Flat instruction for execution — 16 bytes, cache-friendly.
/// Replaces the ~40-byte Instruction enum for the hot interpreter loop.
#[derive(Clone, Copy)]
pub struct Op {
    pub code: u16,
    pub imm: u64,
}

const _: () = assert!(std::mem::size_of::<Op>() == 16);

impl std::fmt::Debug for Op {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Op({}, 0x{:x})", self.code, self.imm)
    }
}

impl Op {
    #[inline(always)]
    pub fn new(code: u16, imm: u64) -> Self {
        Op { code, imm }
    }
    #[inline(always)]
    pub fn unit(code: u16) -> Self {
        Op { code, imm: 0 }
    }
    /// Pack two u32 values into the imm field.
    #[inline(always)]
    pub fn pair(code: u16, hi: u32, lo: u32) -> Self {
        Op {
            code,
            imm: (hi as u64) << 32 | lo as u64,
        }
    }
    #[inline(always)]
    pub fn imm_u32(&self) -> u32 {
        self.imm as u32
    }
    #[inline(always)]
    pub fn imm_i32(&self) -> i32 {
        self.imm as i32
    }
    #[inline(always)]
    pub fn imm_u64(&self) -> u64 {
        self.imm
    }
    #[inline(always)]
    pub fn imm_i64(&self) -> i64 {
        self.imm as i64
    }
    #[inline(always)]
    pub fn imm_f32(&self) -> f32 {
        f32::from_bits(self.imm as u32)
    }
    #[inline(always)]
    pub fn imm_f64(&self) -> f64 {
        f64::from_bits(self.imm)
    }
    #[inline(always)]
    pub fn imm_hi(&self) -> u32 {
        (self.imm >> 32) as u32
    }
    #[inline(always)]
    pub fn imm_lo(&self) -> u32 {
        self.imm as u32
    }
}

// Opcode constants — grouped to match Instruction enum order
// Control
pub const OP_UNREACHABLE: u16 = 0;
pub const OP_NOP: u16 = 1;
pub const OP_BLOCK: u16 = 2; // imm = (end_pc << 32) | arity
pub const OP_LOOP: u16 = 3; // imm = loop_arity
pub const OP_IF: u16 = 4; // imm = (end_pc << 32) | arity (no else)
pub const OP_IF_ELSE: u16 = 5; // imm = (arity << 56) | (end_pc << 28) | else_pc
pub const OP_ELSE: u16 = 6;
pub const OP_END: u16 = 7;
pub const OP_BR: u16 = 8; // imm = depth
pub const OP_BR_IF: u16 = 9; // imm = depth
pub const OP_BR_TABLE: u16 = 10; // imm = index into br_tables
pub const OP_RETURN: u16 = 11;
pub const OP_CALL: u16 = 12; // imm = func_idx
pub const OP_CALL_INDIRECT: u16 = 13; // imm = (type_idx << 32) | table_idx
pub const OP_DROP: u16 = 14;
pub const OP_SELECT: u16 = 15;
// Locals / Globals
pub const OP_LOCAL_GET: u16 = 16; // imm = idx
pub const OP_LOCAL_SET: u16 = 17;
pub const OP_LOCAL_TEE: u16 = 18;
pub const OP_GLOBAL_GET: u16 = 19;
pub const OP_GLOBAL_SET: u16 = 20;
// Memory loads
pub const OP_I32_LOAD: u16 = 21; // imm = offset
pub const OP_I64_LOAD: u16 = 22;
pub const OP_F32_LOAD: u16 = 23;
pub const OP_F64_LOAD: u16 = 24;
pub const OP_I32_LOAD8_S: u16 = 25;
pub const OP_I32_LOAD8_U: u16 = 26;
pub const OP_I32_LOAD16_S: u16 = 27;
pub const OP_I32_LOAD16_U: u16 = 28;
pub const OP_I64_LOAD8_S: u16 = 29;
pub const OP_I64_LOAD8_U: u16 = 30;
pub const OP_I64_LOAD16_S: u16 = 31;
pub const OP_I64_LOAD16_U: u16 = 32;
pub const OP_I64_LOAD32_S: u16 = 33;
pub const OP_I64_LOAD32_U: u16 = 34;
// Memory stores
pub const OP_I32_STORE: u16 = 35;
pub const OP_I64_STORE: u16 = 36;
pub const OP_F32_STORE: u16 = 37;
pub const OP_F64_STORE: u16 = 38;
pub const OP_I32_STORE8: u16 = 39;
pub const OP_I32_STORE16: u16 = 40;
pub const OP_I64_STORE8: u16 = 41;
pub const OP_I64_STORE16: u16 = 42;
pub const OP_I64_STORE32: u16 = 43;
pub const OP_MEMORY_SIZE: u16 = 44;
pub const OP_MEMORY_GROW: u16 = 45;
// Constants
pub const OP_I32_CONST: u16 = 46; // imm = val as u32 as u64
pub const OP_I64_CONST: u16 = 47; // imm = val as u64
pub const OP_F32_CONST: u16 = 48; // imm = val.to_bits() as u64
pub const OP_F64_CONST: u16 = 49; // imm = val.to_bits()
// Superinstructions
pub const OP_LOCAL_GET_I32_CONST: u16 = 50; // imm = (idx << 32) | (val as u32)
pub const OP_LOCAL_GET_LOCAL_GET: u16 = 51; // imm = (a << 32) | b
// i32 comparison
pub const OP_I32_EQZ: u16 = 52;
pub const OP_I32_EQ: u16 = 53;
pub const OP_I32_NE: u16 = 54;
pub const OP_I32_LT_S: u16 = 55;
pub const OP_I32_LT_U: u16 = 56;
pub const OP_I32_GT_S: u16 = 57;
pub const OP_I32_GT_U: u16 = 58;
pub const OP_I32_LE_S: u16 = 59;
pub const OP_I32_LE_U: u16 = 60;
pub const OP_I32_GE_S: u16 = 61;
pub const OP_I32_GE_U: u16 = 62;
// i32 arithmetic
pub const OP_I32_CLZ: u16 = 63;
pub const OP_I32_CTZ: u16 = 64;
pub const OP_I32_POPCNT: u16 = 65;
pub const OP_I32_ADD: u16 = 66;
pub const OP_I32_SUB: u16 = 67;
pub const OP_I32_MUL: u16 = 68;
pub const OP_I32_DIV_S: u16 = 69;
pub const OP_I32_DIV_U: u16 = 70;
pub const OP_I32_REM_S: u16 = 71;
pub const OP_I32_REM_U: u16 = 72;
pub const OP_I32_AND: u16 = 73;
pub const OP_I32_OR: u16 = 74;
pub const OP_I32_XOR: u16 = 75;
pub const OP_I32_SHL: u16 = 76;
pub const OP_I32_SHR_S: u16 = 77;
pub const OP_I32_SHR_U: u16 = 78;
pub const OP_I32_ROTL: u16 = 79;
pub const OP_I32_ROTR: u16 = 80;
// i64 comparison
pub const OP_I64_EQZ: u16 = 81;
pub const OP_I64_EQ: u16 = 82;
pub const OP_I64_NE: u16 = 83;
pub const OP_I64_LT_S: u16 = 84;
pub const OP_I64_LT_U: u16 = 85;
pub const OP_I64_GT_S: u16 = 86;
pub const OP_I64_GT_U: u16 = 87;
pub const OP_I64_LE_S: u16 = 88;
pub const OP_I64_LE_U: u16 = 89;
pub const OP_I64_GE_S: u16 = 90;
pub const OP_I64_GE_U: u16 = 91;
// i64 arithmetic
pub const OP_I64_CLZ: u16 = 92;
pub const OP_I64_CTZ: u16 = 93;
pub const OP_I64_POPCNT: u16 = 94;
pub const OP_I64_ADD: u16 = 95;
pub const OP_I64_SUB: u16 = 96;
pub const OP_I64_MUL: u16 = 97;
pub const OP_I64_DIV_S: u16 = 98;
pub const OP_I64_DIV_U: u16 = 99;
pub const OP_I64_REM_S: u16 = 100;
pub const OP_I64_REM_U: u16 = 101;
pub const OP_I64_AND: u16 = 102;
pub const OP_I64_OR: u16 = 103;
pub const OP_I64_XOR: u16 = 104;
pub const OP_I64_SHL: u16 = 105;
pub const OP_I64_SHR_S: u16 = 106;
pub const OP_I64_SHR_U: u16 = 107;
pub const OP_I64_ROTL: u16 = 108;
pub const OP_I64_ROTR: u16 = 109;
// Conversions
pub const OP_I32_WRAP_I64: u16 = 110;
pub const OP_I64_EXTEND_I32_S: u16 = 111;
pub const OP_I64_EXTEND_I32_U: u16 = 112;
// f32 comparison
pub const OP_F32_EQ: u16 = 113;
pub const OP_F32_NE: u16 = 114;
pub const OP_F32_LT: u16 = 115;
pub const OP_F32_GT: u16 = 116;
pub const OP_F32_LE: u16 = 117;
pub const OP_F32_GE: u16 = 118;
// f64 comparison
pub const OP_F64_EQ: u16 = 119;
pub const OP_F64_NE: u16 = 120;
pub const OP_F64_LT: u16 = 121;
pub const OP_F64_GT: u16 = 122;
pub const OP_F64_LE: u16 = 123;
pub const OP_F64_GE: u16 = 124;
// f32 arithmetic
pub const OP_F32_ABS: u16 = 125;
pub const OP_F32_NEG: u16 = 126;
pub const OP_F32_CEIL: u16 = 127;
pub const OP_F32_FLOOR: u16 = 128;
pub const OP_F32_TRUNC: u16 = 129;
pub const OP_F32_NEAREST: u16 = 130;
pub const OP_F32_SQRT: u16 = 131;
pub const OP_F32_ADD: u16 = 132;
pub const OP_F32_SUB: u16 = 133;
pub const OP_F32_MUL: u16 = 134;
pub const OP_F32_DIV: u16 = 135;
pub const OP_F32_MIN: u16 = 136;
pub const OP_F32_MAX: u16 = 137;
pub const OP_F32_COPYSIGN: u16 = 138;
// f64 arithmetic
pub const OP_F64_ABS: u16 = 139;
pub const OP_F64_NEG: u16 = 140;
pub const OP_F64_CEIL: u16 = 141;
pub const OP_F64_FLOOR: u16 = 142;
pub const OP_F64_TRUNC: u16 = 143;
pub const OP_F64_NEAREST: u16 = 144;
pub const OP_F64_SQRT: u16 = 145;
pub const OP_F64_ADD: u16 = 146;
pub const OP_F64_SUB: u16 = 147;
pub const OP_F64_MUL: u16 = 148;
pub const OP_F64_DIV: u16 = 149;
pub const OP_F64_MIN: u16 = 150;
pub const OP_F64_MAX: u16 = 151;
pub const OP_F64_COPYSIGN: u16 = 152;
// Float-int conversions
pub const OP_I32_TRUNC_F32_S: u16 = 153;
pub const OP_I32_TRUNC_F32_U: u16 = 154;
pub const OP_I32_TRUNC_F64_S: u16 = 155;
pub const OP_I32_TRUNC_F64_U: u16 = 156;
pub const OP_I64_TRUNC_F32_S: u16 = 157;
pub const OP_I64_TRUNC_F32_U: u16 = 158;
pub const OP_I64_TRUNC_F64_S: u16 = 159;
pub const OP_I64_TRUNC_F64_U: u16 = 160;
pub const OP_F32_CONVERT_I32_S: u16 = 161;
pub const OP_F32_CONVERT_I32_U: u16 = 162;
pub const OP_F32_CONVERT_I64_S: u16 = 163;
pub const OP_F32_CONVERT_I64_U: u16 = 164;
pub const OP_F32_DEMOTE_F64: u16 = 165;
pub const OP_F64_CONVERT_I32_S: u16 = 166;
pub const OP_F64_CONVERT_I32_U: u16 = 167;
pub const OP_F64_CONVERT_I64_S: u16 = 168;
pub const OP_F64_CONVERT_I64_U: u16 = 169;
pub const OP_F64_PROMOTE_F32: u16 = 170;
// Reinterpret
pub const OP_I32_REINTERPRET_F32: u16 = 171;
pub const OP_I64_REINTERPRET_F64: u16 = 172;
pub const OP_F32_REINTERPRET_I32: u16 = 173;
pub const OP_F64_REINTERPRET_I64: u16 = 174;
// Sign extension
pub const OP_I32_EXTEND8_S: u16 = 175;
pub const OP_I32_EXTEND16_S: u16 = 176;
pub const OP_I64_EXTEND8_S: u16 = 177;
pub const OP_I64_EXTEND16_S: u16 = 178;
pub const OP_I64_EXTEND32_S: u16 = 179;
// Saturating truncation
pub const OP_I32_TRUNC_SAT_F32_S: u16 = 180;
pub const OP_I32_TRUNC_SAT_F32_U: u16 = 181;
pub const OP_I32_TRUNC_SAT_F64_S: u16 = 182;
pub const OP_I32_TRUNC_SAT_F64_U: u16 = 183;
pub const OP_I64_TRUNC_SAT_F32_S: u16 = 184;
pub const OP_I64_TRUNC_SAT_F32_U: u16 = 185;
pub const OP_I64_TRUNC_SAT_F64_S: u16 = 186;
pub const OP_I64_TRUNC_SAT_F64_U: u16 = 187;
// Reference types / bulk memory
pub const OP_REF_FUNC: u16 = 188; // imm = func_idx
pub const OP_REF_NULL: u16 = 189;
pub const OP_TABLE_INIT: u16 = 190; // imm = (elem_idx << 32) | table_idx
pub const OP_ELEM_DROP: u16 = 191; // imm = elem_idx
pub const OP_REF_IS_NULL: u16 = 192;
pub const OP_MEMORY_INIT: u16 = 193; // imm = data_segment_idx
pub const OP_DATA_DROP: u16 = 194; // imm = data_segment_idx
pub const OP_MEMORY_COPY: u16 = 195;
pub const OP_MEMORY_FILL: u16 = 196;
pub const OP_TABLE_GET: u16 = 197; // imm = table_idx
pub const OP_TABLE_SET: u16 = 198; // imm = table_idx
pub const OP_TABLE_GROW: u16 = 199; // imm = table_idx
pub const OP_TABLE_SIZE: u16 = 200; // imm = table_idx
pub const OP_TABLE_COPY: u16 = 201; // imm = (dst_table << 32) | src_table
pub const OP_TABLE_FILL: u16 = 202; // imm = table_idx

/// Compile a single instruction into an Op.
fn compile_instruction(
    instr: &Instruction,
    types: &[FuncType],
    br_tables: &mut Vec<(Vec<u32>, u32)>,
) -> Op {
    match instr {
        Instruction::Unreachable => Op::unit(OP_UNREACHABLE),
        Instruction::Nop => Op::unit(OP_NOP),
        Instruction::Block { ty, end_pc } => {
            let arity = match ty {
                BlockType::Empty => 0u32,
                BlockType::Val(_) => 1,
                BlockType::FuncType(idx) => types[*idx as usize].results().len() as u32,
            };
            Op::pair(OP_BLOCK, *end_pc as u32, arity)
        }
        Instruction::Loop { ty } => {
            let arity = match ty {
                BlockType::Empty | BlockType::Val(_) => 0u32,
                BlockType::FuncType(idx) => types[*idx as usize].params().len() as u32,
            };
            Op::new(OP_LOOP, arity as u64)
        }
        Instruction::If {
            ty,
            end_pc,
            else_pc,
        } => {
            let arity = match ty {
                BlockType::Empty => 0u32,
                BlockType::Val(_) => 1,
                BlockType::FuncType(idx) => types[*idx as usize].results().len() as u32,
            };
            match else_pc {
                None => Op::pair(OP_IF, *end_pc as u32, arity),
                Some(ep) => {
                    // Pack: (arity << 56) | (end_pc << 28) | else_pc
                    let imm = (arity as u64) << 56 | (*end_pc as u64) << 28 | *ep as u64;
                    Op::new(OP_IF_ELSE, imm)
                }
            }
        }
        Instruction::Else => Op::unit(OP_ELSE),
        Instruction::End => Op::unit(OP_END),
        Instruction::Br(d) => Op::new(OP_BR, *d as u64),
        Instruction::BrIf(d) => Op::new(OP_BR_IF, *d as u64),
        Instruction::BrTable { targets, default } => {
            let idx = br_tables.len();
            br_tables.push((targets.clone(), *default));
            Op::new(OP_BR_TABLE, idx as u64)
        }
        Instruction::Return => Op::unit(OP_RETURN),
        Instruction::Call(idx) => Op::new(OP_CALL, *idx as u64),
        Instruction::CallIndirect {
            type_idx,
            table_idx,
        } => Op::pair(OP_CALL_INDIRECT, *type_idx as u32, *table_idx as u32),
        Instruction::Drop => Op::unit(OP_DROP),
        Instruction::Select => Op::unit(OP_SELECT),
        Instruction::LocalGet(idx) => Op::new(OP_LOCAL_GET, *idx as u64),
        Instruction::LocalSet(idx) => Op::new(OP_LOCAL_SET, *idx as u64),
        Instruction::LocalTee(idx) => Op::new(OP_LOCAL_TEE, *idx as u64),
        Instruction::GlobalGet(idx) => Op::new(OP_GLOBAL_GET, *idx as u64),
        Instruction::GlobalSet(idx) => Op::new(OP_GLOBAL_SET, *idx as u64),
        // Memory loads
        Instruction::I32Load(o) => Op::new(OP_I32_LOAD, *o),
        Instruction::I64Load(o) => Op::new(OP_I64_LOAD, *o),
        Instruction::F32Load(o) => Op::new(OP_F32_LOAD, *o),
        Instruction::F64Load(o) => Op::new(OP_F64_LOAD, *o),
        Instruction::I32Load8S(o) => Op::new(OP_I32_LOAD8_S, *o),
        Instruction::I32Load8U(o) => Op::new(OP_I32_LOAD8_U, *o),
        Instruction::I32Load16S(o) => Op::new(OP_I32_LOAD16_S, *o),
        Instruction::I32Load16U(o) => Op::new(OP_I32_LOAD16_U, *o),
        Instruction::I64Load8S(o) => Op::new(OP_I64_LOAD8_S, *o),
        Instruction::I64Load8U(o) => Op::new(OP_I64_LOAD8_U, *o),
        Instruction::I64Load16S(o) => Op::new(OP_I64_LOAD16_S, *o),
        Instruction::I64Load16U(o) => Op::new(OP_I64_LOAD16_U, *o),
        Instruction::I64Load32S(o) => Op::new(OP_I64_LOAD32_S, *o),
        Instruction::I64Load32U(o) => Op::new(OP_I64_LOAD32_U, *o),
        // Memory stores
        Instruction::I32Store(o) => Op::new(OP_I32_STORE, *o),
        Instruction::I64Store(o) => Op::new(OP_I64_STORE, *o),
        Instruction::F32Store(o) => Op::new(OP_F32_STORE, *o),
        Instruction::F64Store(o) => Op::new(OP_F64_STORE, *o),
        Instruction::I32Store8(o) => Op::new(OP_I32_STORE8, *o),
        Instruction::I32Store16(o) => Op::new(OP_I32_STORE16, *o),
        Instruction::I64Store8(o) => Op::new(OP_I64_STORE8, *o),
        Instruction::I64Store16(o) => Op::new(OP_I64_STORE16, *o),
        Instruction::I64Store32(o) => Op::new(OP_I64_STORE32, *o),
        Instruction::MemorySize => Op::unit(OP_MEMORY_SIZE),
        Instruction::MemoryGrow => Op::unit(OP_MEMORY_GROW),
        // Constants
        Instruction::I32Const(v) => Op::new(OP_I32_CONST, *v as u32 as u64),
        Instruction::I64Const(v) => Op::new(OP_I64_CONST, *v as u64),
        Instruction::F32Const(v) => Op::new(OP_F32_CONST, v.to_bits() as u64),
        Instruction::F64Const(v) => Op::new(OP_F64_CONST, v.to_bits()),
        // Superinstructions
        Instruction::LocalGetI32Const(idx, val) => {
            Op::pair(OP_LOCAL_GET_I32_CONST, *idx, *val as u32)
        }
        Instruction::LocalGetLocalGet(a, b) => Op::pair(OP_LOCAL_GET_LOCAL_GET, *a, *b),
        // All unit ops
        Instruction::I32Eqz => Op::unit(OP_I32_EQZ),
        Instruction::I32Eq => Op::unit(OP_I32_EQ),
        Instruction::I32Ne => Op::unit(OP_I32_NE),
        Instruction::I32LtS => Op::unit(OP_I32_LT_S),
        Instruction::I32LtU => Op::unit(OP_I32_LT_U),
        Instruction::I32GtS => Op::unit(OP_I32_GT_S),
        Instruction::I32GtU => Op::unit(OP_I32_GT_U),
        Instruction::I32LeS => Op::unit(OP_I32_LE_S),
        Instruction::I32LeU => Op::unit(OP_I32_LE_U),
        Instruction::I32GeS => Op::unit(OP_I32_GE_S),
        Instruction::I32GeU => Op::unit(OP_I32_GE_U),
        Instruction::I32Clz => Op::unit(OP_I32_CLZ),
        Instruction::I32Ctz => Op::unit(OP_I32_CTZ),
        Instruction::I32Popcnt => Op::unit(OP_I32_POPCNT),
        Instruction::I32Add => Op::unit(OP_I32_ADD),
        Instruction::I32Sub => Op::unit(OP_I32_SUB),
        Instruction::I32Mul => Op::unit(OP_I32_MUL),
        Instruction::I32DivS => Op::unit(OP_I32_DIV_S),
        Instruction::I32DivU => Op::unit(OP_I32_DIV_U),
        Instruction::I32RemS => Op::unit(OP_I32_REM_S),
        Instruction::I32RemU => Op::unit(OP_I32_REM_U),
        Instruction::I32And => Op::unit(OP_I32_AND),
        Instruction::I32Or => Op::unit(OP_I32_OR),
        Instruction::I32Xor => Op::unit(OP_I32_XOR),
        Instruction::I32Shl => Op::unit(OP_I32_SHL),
        Instruction::I32ShrS => Op::unit(OP_I32_SHR_S),
        Instruction::I32ShrU => Op::unit(OP_I32_SHR_U),
        Instruction::I32Rotl => Op::unit(OP_I32_ROTL),
        Instruction::I32Rotr => Op::unit(OP_I32_ROTR),
        Instruction::I64Eqz => Op::unit(OP_I64_EQZ),
        Instruction::I64Eq => Op::unit(OP_I64_EQ),
        Instruction::I64Ne => Op::unit(OP_I64_NE),
        Instruction::I64LtS => Op::unit(OP_I64_LT_S),
        Instruction::I64LtU => Op::unit(OP_I64_LT_U),
        Instruction::I64GtS => Op::unit(OP_I64_GT_S),
        Instruction::I64GtU => Op::unit(OP_I64_GT_U),
        Instruction::I64LeS => Op::unit(OP_I64_LE_S),
        Instruction::I64LeU => Op::unit(OP_I64_LE_U),
        Instruction::I64GeS => Op::unit(OP_I64_GE_S),
        Instruction::I64GeU => Op::unit(OP_I64_GE_U),
        Instruction::I64Clz => Op::unit(OP_I64_CLZ),
        Instruction::I64Ctz => Op::unit(OP_I64_CTZ),
        Instruction::I64Popcnt => Op::unit(OP_I64_POPCNT),
        Instruction::I64Add => Op::unit(OP_I64_ADD),
        Instruction::I64Sub => Op::unit(OP_I64_SUB),
        Instruction::I64Mul => Op::unit(OP_I64_MUL),
        Instruction::I64DivS => Op::unit(OP_I64_DIV_S),
        Instruction::I64DivU => Op::unit(OP_I64_DIV_U),
        Instruction::I64RemS => Op::unit(OP_I64_REM_S),
        Instruction::I64RemU => Op::unit(OP_I64_REM_U),
        Instruction::I64And => Op::unit(OP_I64_AND),
        Instruction::I64Or => Op::unit(OP_I64_OR),
        Instruction::I64Xor => Op::unit(OP_I64_XOR),
        Instruction::I64Shl => Op::unit(OP_I64_SHL),
        Instruction::I64ShrS => Op::unit(OP_I64_SHR_S),
        Instruction::I64ShrU => Op::unit(OP_I64_SHR_U),
        Instruction::I64Rotl => Op::unit(OP_I64_ROTL),
        Instruction::I64Rotr => Op::unit(OP_I64_ROTR),
        Instruction::I32WrapI64 => Op::unit(OP_I32_WRAP_I64),
        Instruction::I64ExtendI32S => Op::unit(OP_I64_EXTEND_I32_S),
        Instruction::I64ExtendI32U => Op::unit(OP_I64_EXTEND_I32_U),
        Instruction::F32Eq => Op::unit(OP_F32_EQ),
        Instruction::F32Ne => Op::unit(OP_F32_NE),
        Instruction::F32Lt => Op::unit(OP_F32_LT),
        Instruction::F32Gt => Op::unit(OP_F32_GT),
        Instruction::F32Le => Op::unit(OP_F32_LE),
        Instruction::F32Ge => Op::unit(OP_F32_GE),
        Instruction::F64Eq => Op::unit(OP_F64_EQ),
        Instruction::F64Ne => Op::unit(OP_F64_NE),
        Instruction::F64Lt => Op::unit(OP_F64_LT),
        Instruction::F64Gt => Op::unit(OP_F64_GT),
        Instruction::F64Le => Op::unit(OP_F64_LE),
        Instruction::F64Ge => Op::unit(OP_F64_GE),
        Instruction::F32Abs => Op::unit(OP_F32_ABS),
        Instruction::F32Neg => Op::unit(OP_F32_NEG),
        Instruction::F32Ceil => Op::unit(OP_F32_CEIL),
        Instruction::F32Floor => Op::unit(OP_F32_FLOOR),
        Instruction::F32Trunc => Op::unit(OP_F32_TRUNC),
        Instruction::F32Nearest => Op::unit(OP_F32_NEAREST),
        Instruction::F32Sqrt => Op::unit(OP_F32_SQRT),
        Instruction::F32Add => Op::unit(OP_F32_ADD),
        Instruction::F32Sub => Op::unit(OP_F32_SUB),
        Instruction::F32Mul => Op::unit(OP_F32_MUL),
        Instruction::F32Div => Op::unit(OP_F32_DIV),
        Instruction::F32Min => Op::unit(OP_F32_MIN),
        Instruction::F32Max => Op::unit(OP_F32_MAX),
        Instruction::F32Copysign => Op::unit(OP_F32_COPYSIGN),
        Instruction::F64Abs => Op::unit(OP_F64_ABS),
        Instruction::F64Neg => Op::unit(OP_F64_NEG),
        Instruction::F64Ceil => Op::unit(OP_F64_CEIL),
        Instruction::F64Floor => Op::unit(OP_F64_FLOOR),
        Instruction::F64Trunc => Op::unit(OP_F64_TRUNC),
        Instruction::F64Nearest => Op::unit(OP_F64_NEAREST),
        Instruction::F64Sqrt => Op::unit(OP_F64_SQRT),
        Instruction::F64Add => Op::unit(OP_F64_ADD),
        Instruction::F64Sub => Op::unit(OP_F64_SUB),
        Instruction::F64Mul => Op::unit(OP_F64_MUL),
        Instruction::F64Div => Op::unit(OP_F64_DIV),
        Instruction::F64Min => Op::unit(OP_F64_MIN),
        Instruction::F64Max => Op::unit(OP_F64_MAX),
        Instruction::F64Copysign => Op::unit(OP_F64_COPYSIGN),
        Instruction::I32TruncF32S => Op::unit(OP_I32_TRUNC_F32_S),
        Instruction::I32TruncF32U => Op::unit(OP_I32_TRUNC_F32_U),
        Instruction::I32TruncF64S => Op::unit(OP_I32_TRUNC_F64_S),
        Instruction::I32TruncF64U => Op::unit(OP_I32_TRUNC_F64_U),
        Instruction::I64TruncF32S => Op::unit(OP_I64_TRUNC_F32_S),
        Instruction::I64TruncF32U => Op::unit(OP_I64_TRUNC_F32_U),
        Instruction::I64TruncF64S => Op::unit(OP_I64_TRUNC_F64_S),
        Instruction::I64TruncF64U => Op::unit(OP_I64_TRUNC_F64_U),
        Instruction::F32ConvertI32S => Op::unit(OP_F32_CONVERT_I32_S),
        Instruction::F32ConvertI32U => Op::unit(OP_F32_CONVERT_I32_U),
        Instruction::F32ConvertI64S => Op::unit(OP_F32_CONVERT_I64_S),
        Instruction::F32ConvertI64U => Op::unit(OP_F32_CONVERT_I64_U),
        Instruction::F32DemoteF64 => Op::unit(OP_F32_DEMOTE_F64),
        Instruction::F64ConvertI32S => Op::unit(OP_F64_CONVERT_I32_S),
        Instruction::F64ConvertI32U => Op::unit(OP_F64_CONVERT_I32_U),
        Instruction::F64ConvertI64S => Op::unit(OP_F64_CONVERT_I64_S),
        Instruction::F64ConvertI64U => Op::unit(OP_F64_CONVERT_I64_U),
        Instruction::F64PromoteF32 => Op::unit(OP_F64_PROMOTE_F32),
        Instruction::I32ReinterpretF32 => Op::unit(OP_I32_REINTERPRET_F32),
        Instruction::I64ReinterpretF64 => Op::unit(OP_I64_REINTERPRET_F64),
        Instruction::F32ReinterpretI32 => Op::unit(OP_F32_REINTERPRET_I32),
        Instruction::F64ReinterpretI64 => Op::unit(OP_F64_REINTERPRET_I64),
        Instruction::I32Extend8S => Op::unit(OP_I32_EXTEND8_S),
        Instruction::I32Extend16S => Op::unit(OP_I32_EXTEND16_S),
        Instruction::I64Extend8S => Op::unit(OP_I64_EXTEND8_S),
        Instruction::I64Extend16S => Op::unit(OP_I64_EXTEND16_S),
        Instruction::I64Extend32S => Op::unit(OP_I64_EXTEND32_S),
        Instruction::I32TruncSatF32S => Op::unit(OP_I32_TRUNC_SAT_F32_S),
        Instruction::I32TruncSatF32U => Op::unit(OP_I32_TRUNC_SAT_F32_U),
        Instruction::I32TruncSatF64S => Op::unit(OP_I32_TRUNC_SAT_F64_S),
        Instruction::I32TruncSatF64U => Op::unit(OP_I32_TRUNC_SAT_F64_U),
        Instruction::I64TruncSatF32S => Op::unit(OP_I64_TRUNC_SAT_F32_S),
        Instruction::I64TruncSatF32U => Op::unit(OP_I64_TRUNC_SAT_F32_U),
        Instruction::I64TruncSatF64S => Op::unit(OP_I64_TRUNC_SAT_F64_S),
        Instruction::I64TruncSatF64U => Op::unit(OP_I64_TRUNC_SAT_F64_U),
        Instruction::RefFunc(idx) => Op::new(OP_REF_FUNC, *idx as u64),
        Instruction::RefNull => Op::unit(OP_REF_NULL),
        Instruction::RefIsNull => Op::unit(OP_REF_IS_NULL),
        Instruction::TableInit {
            elem_idx,
            table_idx,
        } => Op::pair(OP_TABLE_INIT, *elem_idx, *table_idx),
        Instruction::ElemDrop(idx) => Op::new(OP_ELEM_DROP, *idx as u64),
        Instruction::MemoryInit(idx) => Op::new(OP_MEMORY_INIT, *idx as u64),
        Instruction::DataDrop(idx) => Op::new(OP_DATA_DROP, *idx as u64),
        Instruction::MemoryCopy => Op::unit(OP_MEMORY_COPY),
        Instruction::MemoryFill => Op::unit(OP_MEMORY_FILL),
        Instruction::TableGet(idx) => Op::new(OP_TABLE_GET, *idx as u64),
        Instruction::TableSet(idx) => Op::new(OP_TABLE_SET, *idx as u64),
        Instruction::TableGrow(idx) => Op::new(OP_TABLE_GROW, *idx as u64),
        Instruction::TableSize(idx) => Op::new(OP_TABLE_SIZE, *idx as u64),
        Instruction::TableCopy {
            dst_table,
            src_table,
        } => Op::pair(OP_TABLE_COPY, *dst_table, *src_table),
        Instruction::TableFill(idx) => Op::new(OP_TABLE_FILL, *idx as u64),
    }
}

/// Compile a Vec<Instruction> into flat Ops, pre-computing block arities.
/// Returns (ops, br_tables) where br_tables stores BrTable target data out-of-line.
pub fn compile_body(instrs: &[Instruction], types: &[FuncType]) -> (Vec<Op>, Vec<(Vec<u32>, u32)>) {
    let mut ops = Vec::with_capacity(instrs.len());
    let mut br_tables = Vec::new();
    for instr in instrs {
        let op = compile_instruction(instr, types, &mut br_tables);
        ops.push(op);
    }
    (ops, br_tables)
}
