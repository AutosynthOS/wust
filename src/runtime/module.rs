use wasmparser::{
    FuncType, Operator, Parser, Payload, ValType,
};

/// A parsed WASM module — types, functions, memory, etc.
/// This is the immutable "code" side. Instance state lives in Store.
#[derive(Debug)]
pub struct Module {
    pub types: Vec<FuncType>,
    pub funcs: Vec<Func>,
    pub memories: Vec<MemoryType>,
    pub globals: Vec<GlobalDef>,
    pub exports: Vec<Export>,
    pub data_segments: Vec<DataSegment>,
    pub tables: Vec<TableDef>,
    pub elements: Vec<ElemSegment>,
    pub start: Option<u32>,
    /// func_types[i] = index into self.types for function i
    /// (includes imports — imports come first)
    pub func_types: Vec<u32>,
    /// Import counts — imported items come first in the index space.
    pub num_func_imports: u32,
    pub num_global_imports: u32,
    pub num_memory_imports: u32,
    pub num_table_imports: u32,
    /// Import descriptors (module, field, kind).
    pub imports: Vec<Import>,
}

#[derive(Debug, Clone)]
pub struct Import {
    pub module: String,
    pub name: String,
    pub kind: ImportKind,
}

#[derive(Debug, Clone)]
pub enum ImportKind {
    Func(u32),       // type index
    Global { ty: ValType, mutable: bool },
    Memory(MemoryType),
    Table(TableDef),
}

#[derive(Debug)]
pub struct Func {
    pub type_idx: u32,
    pub locals: Vec<ValType>,
    pub body: Vec<Op>,
    /// Out-of-line BrTable data: (targets, default) indexed by Op.imm for OP_BR_TABLE.
    pub br_tables: Vec<(Vec<u32>, u32)>,
}

#[derive(Debug, Clone)]
pub struct MemoryType {
    pub min: u64,
    pub max: Option<u64>,
}

#[derive(Debug)]
pub struct GlobalDef {
    pub ty: ValType,
    pub mutable: bool,
    pub init: Instruction,
}

#[derive(Debug, Clone)]
pub struct Export {
    pub name: String,
    pub kind: ExportKind,
    pub index: u32,
}

#[derive(Debug, Clone)]
pub enum ExportKind {
    Func,
    Memory,
    Global,
    Table,
}

#[derive(Debug)]
pub struct DataSegment {
    pub offset: Instruction,
    pub data: Vec<u8>,
}

#[derive(Debug, Clone)]
pub struct TableDef {
    pub min: u64,
    pub max: Option<u64>,
}

#[derive(Debug)]
pub struct ElemSegment {
    pub table_idx: u32,
    pub offset: Vec<Instruction>,
    pub func_indices: Vec<u32>,
}

/// Our own instruction enum — decoded from wasmparser's Operator once at parse
/// time so we don't re-parse during execution.
#[derive(Debug, Clone)]
pub enum Instruction {
    // Control
    Unreachable,
    Nop,
    Block { ty: BlockType, end_pc: usize },
    Loop { ty: BlockType },
    If { ty: BlockType, end_pc: usize, else_pc: Option<usize> },
    Else,
    End,
    Br(u32),
    BrIf(u32),
    BrTable { targets: Vec<u32>, default: u32 },
    Return,
    Call(u32),
    CallIndirect { type_idx: u32, table_idx: u32 },
    Drop,
    Select,

    // Locals / Globals
    LocalGet(u32),
    LocalSet(u32),
    LocalTee(u32),
    GlobalGet(u32),
    GlobalSet(u32),

    // Memory (align is a hint per spec — not stored)
    I32Load(u64),
    I64Load(u64),
    F32Load(u64),
    F64Load(u64),
    I32Load8S(u64),
    I32Load8U(u64),
    I32Load16S(u64),
    I32Load16U(u64),
    I64Load8S(u64),
    I64Load8U(u64),
    I64Load16S(u64),
    I64Load16U(u64),
    I64Load32S(u64),
    I64Load32U(u64),
    I32Store(u64),
    I64Store(u64),
    F32Store(u64),
    F64Store(u64),
    I32Store8(u64),
    I32Store16(u64),
    I64Store8(u64),
    I64Store16(u64),
    I64Store32(u64),
    MemorySize,
    MemoryGrow,

    // Constants
    I32Const(i32),
    I64Const(i64),
    F32Const(f32),
    F64Const(f64),

    // Superinstructions (fused sequences for hot paths)
    /// LocalGet(idx) + I32Const(val) — pushes local then constant
    LocalGetI32Const(u32, i32),
    /// LocalGet(a) + LocalGet(b) — pushes two locals
    LocalGetLocalGet(u32, u32),

    // i32 arithmetic
    I32Eqz,
    I32Eq,
    I32Ne,
    I32LtS,
    I32LtU,
    I32GtS,
    I32GtU,
    I32LeS,
    I32LeU,
    I32GeS,
    I32GeU,
    I32Clz,
    I32Ctz,
    I32Popcnt,
    I32Add,
    I32Sub,
    I32Mul,
    I32DivS,
    I32DivU,
    I32RemS,
    I32RemU,
    I32And,
    I32Or,
    I32Xor,
    I32Shl,
    I32ShrS,
    I32ShrU,
    I32Rotl,
    I32Rotr,

    // i64 arithmetic
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
    I64Clz,
    I64Ctz,
    I64Popcnt,
    I64Add,
    I64Sub,
    I64Mul,
    I64DivS,
    I64DivU,
    I64RemS,
    I64RemU,
    I64And,
    I64Or,
    I64Xor,
    I64Shl,
    I64ShrS,
    I64ShrU,
    I64Rotl,
    I64Rotr,

    // Conversions
    I32WrapI64,
    I64ExtendI32S,
    I64ExtendI32U,

    // f32 comparison
    F32Eq,
    F32Ne,
    F32Lt,
    F32Gt,
    F32Le,
    F32Ge,
    F64Eq,
    F64Ne,
    F64Lt,
    F64Gt,
    F64Le,
    F64Ge,
    F32Abs,
    F32Neg,
    F32Ceil,
    F32Floor,
    F32Trunc,
    F32Nearest,
    F32Sqrt,
    F32Add,
    F32Sub,
    F32Mul,
    F32Div,
    F32Min,
    F32Max,
    F32Copysign,
    F64Abs,
    F64Neg,
    F64Ceil,
    F64Floor,
    F64Trunc,
    F64Nearest,
    F64Sqrt,
    F64Add,
    F64Sub,
    F64Mul,
    F64Div,
    F64Min,
    F64Max,
    F64Copysign,

    // More conversions
    I32TruncF32S,
    I32TruncF32U,
    I32TruncF64S,
    I32TruncF64U,
    I64TruncF32S,
    I64TruncF32U,
    I64TruncF64S,
    I64TruncF64U,
    F32ConvertI32S,
    F32ConvertI32U,
    F32ConvertI64S,
    F32ConvertI64U,
    F32DemoteF64,
    F64ConvertI32S,
    F64ConvertI32U,
    F64ConvertI64S,
    F64ConvertI64U,
    F64PromoteF32,
    I32ReinterpretF32,
    I64ReinterpretF64,
    F32ReinterpretI32,
    F64ReinterpretI64,

    // Sign extension
    I32Extend8S,
    I32Extend16S,
    I64Extend8S,
    I64Extend16S,
    I64Extend32S,

    // Bulk memory operations
    TableInit { elem_idx: u32, table_idx: u32 },
    ElemDrop(u32),

    // Saturating truncation
    I32TruncSatF32S,
    I32TruncSatF32U,
    I32TruncSatF64S,
    I32TruncSatF64U,
    I64TruncSatF32S,
    I64TruncSatF32U,
    I64TruncSatF64S,
    I64TruncSatF64U,
}

#[derive(Debug, Clone)]
pub enum BlockType {
    Empty,
    Val(ValType),
    FuncType(u32),
}

/// Flat instruction for execution — 16 bytes, cache-friendly.
/// Replaces the ~40-byte Instruction enum for the hot interpreter loop.
#[derive(Clone, Copy)]
pub struct Op {
    pub code: u8,
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
    pub fn new(code: u8, imm: u64) -> Self { Op { code, imm } }
    #[inline(always)]
    pub fn unit(code: u8) -> Self { Op { code, imm: 0 } }
    /// Pack two u32 values into the imm field.
    #[inline(always)]
    pub fn pair(code: u8, hi: u32, lo: u32) -> Self {
        Op { code, imm: (hi as u64) << 32 | lo as u64 }
    }
    #[inline(always)]
    pub fn imm_u32(&self) -> u32 { self.imm as u32 }
    #[inline(always)]
    pub fn imm_i32(&self) -> i32 { self.imm as i32 }
    #[inline(always)]
    pub fn imm_u64(&self) -> u64 { self.imm }
    #[inline(always)]
    pub fn imm_i64(&self) -> i64 { self.imm as i64 }
    #[inline(always)]
    pub fn imm_f32(&self) -> f32 { f32::from_bits(self.imm as u32) }
    #[inline(always)]
    pub fn imm_f64(&self) -> f64 { f64::from_bits(self.imm) }
    #[inline(always)]
    pub fn imm_hi(&self) -> u32 { (self.imm >> 32) as u32 }
    #[inline(always)]
    pub fn imm_lo(&self) -> u32 { self.imm as u32 }
}

// Opcode constants — grouped to match Instruction enum order
// Control
pub const OP_UNREACHABLE: u8 = 0;
pub const OP_NOP: u8 = 1;
pub const OP_BLOCK: u8 = 2;           // imm = (end_pc << 32) | arity
pub const OP_LOOP: u8 = 3;            // imm = loop_arity
pub const OP_IF: u8 = 4;              // imm = (end_pc << 32) | arity (no else)
pub const OP_IF_ELSE: u8 = 5;         // imm = (arity << 56) | (end_pc << 28) | else_pc
pub const OP_ELSE: u8 = 6;
pub const OP_END: u8 = 7;
pub const OP_BR: u8 = 8;              // imm = depth
pub const OP_BR_IF: u8 = 9;           // imm = depth
pub const OP_BR_TABLE: u8 = 10;       // imm = index into br_tables
pub const OP_RETURN: u8 = 11;
pub const OP_CALL: u8 = 12;           // imm = func_idx
pub const OP_CALL_INDIRECT: u8 = 13;  // imm = (type_idx << 32) | table_idx
pub const OP_DROP: u8 = 14;
pub const OP_SELECT: u8 = 15;
// Locals / Globals
pub const OP_LOCAL_GET: u8 = 16;      // imm = idx
pub const OP_LOCAL_SET: u8 = 17;
pub const OP_LOCAL_TEE: u8 = 18;
pub const OP_GLOBAL_GET: u8 = 19;
pub const OP_GLOBAL_SET: u8 = 20;
// Memory loads
pub const OP_I32_LOAD: u8 = 21;       // imm = offset
pub const OP_I64_LOAD: u8 = 22;
pub const OP_F32_LOAD: u8 = 23;
pub const OP_F64_LOAD: u8 = 24;
pub const OP_I32_LOAD8_S: u8 = 25;
pub const OP_I32_LOAD8_U: u8 = 26;
pub const OP_I32_LOAD16_S: u8 = 27;
pub const OP_I32_LOAD16_U: u8 = 28;
pub const OP_I64_LOAD8_S: u8 = 29;
pub const OP_I64_LOAD8_U: u8 = 30;
pub const OP_I64_LOAD16_S: u8 = 31;
pub const OP_I64_LOAD16_U: u8 = 32;
pub const OP_I64_LOAD32_S: u8 = 33;
pub const OP_I64_LOAD32_U: u8 = 34;
// Memory stores
pub const OP_I32_STORE: u8 = 35;
pub const OP_I64_STORE: u8 = 36;
pub const OP_F32_STORE: u8 = 37;
pub const OP_F64_STORE: u8 = 38;
pub const OP_I32_STORE8: u8 = 39;
pub const OP_I32_STORE16: u8 = 40;
pub const OP_I64_STORE8: u8 = 41;
pub const OP_I64_STORE16: u8 = 42;
pub const OP_I64_STORE32: u8 = 43;
pub const OP_MEMORY_SIZE: u8 = 44;
pub const OP_MEMORY_GROW: u8 = 45;
// Constants
pub const OP_I32_CONST: u8 = 46;      // imm = val as u32 as u64
pub const OP_I64_CONST: u8 = 47;      // imm = val as u64
pub const OP_F32_CONST: u8 = 48;      // imm = val.to_bits() as u64
pub const OP_F64_CONST: u8 = 49;      // imm = val.to_bits()
// Superinstructions
pub const OP_LOCAL_GET_I32_CONST: u8 = 50; // imm = (idx << 32) | (val as u32)
pub const OP_LOCAL_GET_LOCAL_GET: u8 = 51; // imm = (a << 32) | b
// i32 comparison
pub const OP_I32_EQZ: u8 = 52;
pub const OP_I32_EQ: u8 = 53;
pub const OP_I32_NE: u8 = 54;
pub const OP_I32_LT_S: u8 = 55;
pub const OP_I32_LT_U: u8 = 56;
pub const OP_I32_GT_S: u8 = 57;
pub const OP_I32_GT_U: u8 = 58;
pub const OP_I32_LE_S: u8 = 59;
pub const OP_I32_LE_U: u8 = 60;
pub const OP_I32_GE_S: u8 = 61;
pub const OP_I32_GE_U: u8 = 62;
// i32 arithmetic
pub const OP_I32_CLZ: u8 = 63;
pub const OP_I32_CTZ: u8 = 64;
pub const OP_I32_POPCNT: u8 = 65;
pub const OP_I32_ADD: u8 = 66;
pub const OP_I32_SUB: u8 = 67;
pub const OP_I32_MUL: u8 = 68;
pub const OP_I32_DIV_S: u8 = 69;
pub const OP_I32_DIV_U: u8 = 70;
pub const OP_I32_REM_S: u8 = 71;
pub const OP_I32_REM_U: u8 = 72;
pub const OP_I32_AND: u8 = 73;
pub const OP_I32_OR: u8 = 74;
pub const OP_I32_XOR: u8 = 75;
pub const OP_I32_SHL: u8 = 76;
pub const OP_I32_SHR_S: u8 = 77;
pub const OP_I32_SHR_U: u8 = 78;
pub const OP_I32_ROTL: u8 = 79;
pub const OP_I32_ROTR: u8 = 80;
// i64 comparison
pub const OP_I64_EQZ: u8 = 81;
pub const OP_I64_EQ: u8 = 82;
pub const OP_I64_NE: u8 = 83;
pub const OP_I64_LT_S: u8 = 84;
pub const OP_I64_LT_U: u8 = 85;
pub const OP_I64_GT_S: u8 = 86;
pub const OP_I64_GT_U: u8 = 87;
pub const OP_I64_LE_S: u8 = 88;
pub const OP_I64_LE_U: u8 = 89;
pub const OP_I64_GE_S: u8 = 90;
pub const OP_I64_GE_U: u8 = 91;
// i64 arithmetic
pub const OP_I64_CLZ: u8 = 92;
pub const OP_I64_CTZ: u8 = 93;
pub const OP_I64_POPCNT: u8 = 94;
pub const OP_I64_ADD: u8 = 95;
pub const OP_I64_SUB: u8 = 96;
pub const OP_I64_MUL: u8 = 97;
pub const OP_I64_DIV_S: u8 = 98;
pub const OP_I64_DIV_U: u8 = 99;
pub const OP_I64_REM_S: u8 = 100;
pub const OP_I64_REM_U: u8 = 101;
pub const OP_I64_AND: u8 = 102;
pub const OP_I64_OR: u8 = 103;
pub const OP_I64_XOR: u8 = 104;
pub const OP_I64_SHL: u8 = 105;
pub const OP_I64_SHR_S: u8 = 106;
pub const OP_I64_SHR_U: u8 = 107;
pub const OP_I64_ROTL: u8 = 108;
pub const OP_I64_ROTR: u8 = 109;
// Conversions
pub const OP_I32_WRAP_I64: u8 = 110;
pub const OP_I64_EXTEND_I32_S: u8 = 111;
pub const OP_I64_EXTEND_I32_U: u8 = 112;
// f32 comparison
pub const OP_F32_EQ: u8 = 113;
pub const OP_F32_NE: u8 = 114;
pub const OP_F32_LT: u8 = 115;
pub const OP_F32_GT: u8 = 116;
pub const OP_F32_LE: u8 = 117;
pub const OP_F32_GE: u8 = 118;
// f64 comparison
pub const OP_F64_EQ: u8 = 119;
pub const OP_F64_NE: u8 = 120;
pub const OP_F64_LT: u8 = 121;
pub const OP_F64_GT: u8 = 122;
pub const OP_F64_LE: u8 = 123;
pub const OP_F64_GE: u8 = 124;
// f32 arithmetic
pub const OP_F32_ABS: u8 = 125;
pub const OP_F32_NEG: u8 = 126;
pub const OP_F32_CEIL: u8 = 127;
pub const OP_F32_FLOOR: u8 = 128;
pub const OP_F32_TRUNC: u8 = 129;
pub const OP_F32_NEAREST: u8 = 130;
pub const OP_F32_SQRT: u8 = 131;
pub const OP_F32_ADD: u8 = 132;
pub const OP_F32_SUB: u8 = 133;
pub const OP_F32_MUL: u8 = 134;
pub const OP_F32_DIV: u8 = 135;
pub const OP_F32_MIN: u8 = 136;
pub const OP_F32_MAX: u8 = 137;
pub const OP_F32_COPYSIGN: u8 = 138;
// f64 arithmetic
pub const OP_F64_ABS: u8 = 139;
pub const OP_F64_NEG: u8 = 140;
pub const OP_F64_CEIL: u8 = 141;
pub const OP_F64_FLOOR: u8 = 142;
pub const OP_F64_TRUNC: u8 = 143;
pub const OP_F64_NEAREST: u8 = 144;
pub const OP_F64_SQRT: u8 = 145;
pub const OP_F64_ADD: u8 = 146;
pub const OP_F64_SUB: u8 = 147;
pub const OP_F64_MUL: u8 = 148;
pub const OP_F64_DIV: u8 = 149;
pub const OP_F64_MIN: u8 = 150;
pub const OP_F64_MAX: u8 = 151;
pub const OP_F64_COPYSIGN: u8 = 152;
// Float-int conversions
pub const OP_I32_TRUNC_F32_S: u8 = 153;
pub const OP_I32_TRUNC_F32_U: u8 = 154;
pub const OP_I32_TRUNC_F64_S: u8 = 155;
pub const OP_I32_TRUNC_F64_U: u8 = 156;
pub const OP_I64_TRUNC_F32_S: u8 = 157;
pub const OP_I64_TRUNC_F32_U: u8 = 158;
pub const OP_I64_TRUNC_F64_S: u8 = 159;
pub const OP_I64_TRUNC_F64_U: u8 = 160;
pub const OP_F32_CONVERT_I32_S: u8 = 161;
pub const OP_F32_CONVERT_I32_U: u8 = 162;
pub const OP_F32_CONVERT_I64_S: u8 = 163;
pub const OP_F32_CONVERT_I64_U: u8 = 164;
pub const OP_F32_DEMOTE_F64: u8 = 165;
pub const OP_F64_CONVERT_I32_S: u8 = 166;
pub const OP_F64_CONVERT_I32_U: u8 = 167;
pub const OP_F64_CONVERT_I64_S: u8 = 168;
pub const OP_F64_CONVERT_I64_U: u8 = 169;
pub const OP_F64_PROMOTE_F32: u8 = 170;
// Reinterpret
pub const OP_I32_REINTERPRET_F32: u8 = 171;
pub const OP_I64_REINTERPRET_F64: u8 = 172;
pub const OP_F32_REINTERPRET_I32: u8 = 173;
pub const OP_F64_REINTERPRET_I64: u8 = 174;
// Sign extension
pub const OP_I32_EXTEND8_S: u8 = 175;
pub const OP_I32_EXTEND16_S: u8 = 176;
pub const OP_I64_EXTEND8_S: u8 = 177;
pub const OP_I64_EXTEND16_S: u8 = 178;
pub const OP_I64_EXTEND32_S: u8 = 179;
// Saturating truncation
pub const OP_I32_TRUNC_SAT_F32_S: u8 = 180;
pub const OP_I32_TRUNC_SAT_F32_U: u8 = 181;
pub const OP_I32_TRUNC_SAT_F64_S: u8 = 182;
pub const OP_I32_TRUNC_SAT_F64_U: u8 = 183;
pub const OP_I64_TRUNC_SAT_F32_S: u8 = 184;
pub const OP_I64_TRUNC_SAT_F32_U: u8 = 185;
pub const OP_I64_TRUNC_SAT_F64_S: u8 = 186;
pub const OP_I64_TRUNC_SAT_F64_U: u8 = 187;
// Bulk memory operations
pub const OP_TABLE_INIT: u8 = 188;      // imm = (elem_idx << 32) | table_idx
pub const OP_ELEM_DROP: u8 = 189;       // imm = elem_idx

/// Compile a Vec<Instruction> into flat Ops, pre-computing block arities.
/// Returns (ops, br_tables) where br_tables stores BrTable target data out-of-line.
fn compile_body(instrs: &[Instruction], types: &[FuncType]) -> (Vec<Op>, Vec<(Vec<u32>, u32)>) {
    let mut ops = Vec::with_capacity(instrs.len());
    let mut br_tables = Vec::new();
    for instr in instrs {
        let op = match instr {
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
            Instruction::If { ty, end_pc, else_pc } => {
                let arity = match ty {
                    BlockType::Empty => 0u32,
                    BlockType::Val(_) => 1,
                    BlockType::FuncType(idx) => types[*idx as usize].results().len() as u32,
                };
                match else_pc {
                    None => Op::pair(OP_IF, *end_pc as u32, arity),
                    Some(ep) => {
                        // Pack: (arity << 56) | (end_pc << 28) | else_pc
                        let imm = (arity as u64) << 56
                            | (*end_pc as u64) << 28
                            | *ep as u64;
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
            Instruction::CallIndirect { type_idx, table_idx } => {
                Op::pair(OP_CALL_INDIRECT, *type_idx as u32, *table_idx as u32)
            }
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
            Instruction::LocalGetLocalGet(a, b) => {
                Op::pair(OP_LOCAL_GET_LOCAL_GET, *a, *b)
            }
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
            Instruction::TableInit { elem_idx, table_idx } => {
                Op::pair(OP_TABLE_INIT, *elem_idx, *table_idx)
            }
            Instruction::ElemDrop(idx) => Op::new(OP_ELEM_DROP, *idx as u64),
        };
        ops.push(op);
    }
    (ops, br_tables)
}

impl Module {
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        let parser = Parser::new(0);
        let mut types = Vec::new();
        let mut funcs = Vec::new();
        let mut memories = Vec::new();
        let mut globals = Vec::new();
        let mut exports = Vec::new();
        let mut data_segments = Vec::new();
        let mut func_types = Vec::new();
        let mut tables = Vec::new();
        let mut elements = Vec::new();
        let mut start = None;
        let mut code_idx = 0u32;
        let mut imports = Vec::new();
        let mut num_func_imports = 0u32;
        let mut num_global_imports = 0u32;
        let mut num_memory_imports = 0u32;
        let mut num_table_imports = 0u32;

        // Collect function bodies separately, then zip with types
        let mut func_bodies: Vec<(Vec<ValType>, Vec<Instruction>)> = Vec::new();

        for payload in parser.parse_all(bytes) {
            let payload = payload.map_err(|e| format!("parse error: {e}"))?;
            match payload {
                Payload::ImportSection(reader) => {
                    for import in reader {
                        let import = import.map_err(|e| format!("import error: {e}"))?;
                        let kind = match import.ty {
                            wasmparser::TypeRef::Func(idx) => {
                                func_types.push(idx);
                                num_func_imports += 1;
                                ImportKind::Func(idx)
                            }
                            wasmparser::TypeRef::Global(ty) => {
                                num_global_imports += 1;
                                ImportKind::Global { ty: ty.content_type, mutable: ty.mutable }
                            }
                            wasmparser::TypeRef::Memory(ty) => {
                                memories.push(MemoryType { min: ty.initial, max: ty.maximum });
                                num_memory_imports += 1;
                                ImportKind::Memory(MemoryType { min: ty.initial, max: ty.maximum })
                            }
                            wasmparser::TypeRef::Table(ty) => {
                                tables.push(TableDef { min: ty.initial, max: ty.maximum });
                                num_table_imports += 1;
                                ImportKind::Table(TableDef { min: ty.initial, max: ty.maximum })
                            }
                            _ => continue,
                        };
                        imports.push(Import {
                            module: import.module.to_string(),
                            name: import.name.to_string(),
                            kind,
                        });
                    }
                }
                Payload::TypeSection(reader) => {
                    for ty in reader.into_iter_err_on_gc_types() {
                        let ty = ty.map_err(|e| format!("type error: {e}"))?;
                        types.push(ty.clone());
                    }
                }
                Payload::FunctionSection(reader) => {
                    for type_idx in reader {
                        let type_idx = type_idx.map_err(|e| format!("func error: {e}"))?;
                        func_types.push(type_idx);
                    }
                }
                Payload::MemorySection(reader) => {
                    for mem in reader {
                        let mem = mem.map_err(|e| format!("memory error: {e}"))?;
                        memories.push(MemoryType {
                            min: mem.initial,
                            max: mem.maximum,
                        });
                    }
                }
                Payload::GlobalSection(reader) => {
                    for global in reader {
                        let global = global.map_err(|e| format!("global error: {e}"))?;
                        let init = decode_const_expr(&global.init_expr)?;
                        globals.push(GlobalDef {
                            ty: global.ty.content_type,
                            mutable: global.ty.mutable,
                            init,
                        });
                    }
                }
                Payload::TableSection(reader) => {
                    for table in reader {
                        let table = table.map_err(|e| format!("table error: {e}"))?;
                        tables.push(TableDef {
                            min: table.ty.initial,
                            max: table.ty.maximum,
                        });
                    }
                }
                Payload::ElementSection(reader) => {
                    for elem in reader {
                        let elem = elem.map_err(|e| format!("element error: {e}"))?;
                        if let wasmparser::ElementKind::Active {
                            table_index,
                            offset_expr,
                        } = elem.kind
                        {
                            let table_idx = table_index.unwrap_or(0);
                            let offset = decode_const_expr_multi(&offset_expr)?;
                            let mut func_indices = Vec::new();
                            match elem.items {
                                wasmparser::ElementItems::Functions(reader) => {
                                    for idx in reader {
                                        let idx = idx.map_err(|e| format!("elem func error: {e}"))?;
                                        func_indices.push(idx);
                                    }
                                }
                                wasmparser::ElementItems::Expressions(_, reader) => {
                                    for expr in reader {
                                        let expr = expr.map_err(|e| format!("elem expr error: {e}"))?;
                                        let mut expr_reader = expr.get_operators_reader();
                                        let mut found = false;
                                        while let Ok(op) = expr_reader.read() {
                                            match op {
                                                Operator::RefFunc { function_index } => {
                                                    func_indices.push(function_index);
                                                    found = true;
                                                    break;
                                                }
                                                Operator::I32Const { value } => {
                                                    func_indices.push(value as u32);
                                                    found = true;
                                                    break;
                                                }
                                                Operator::End => break,
                                                _ => {}
                                            }
                                        }
                                        if !found {
                                            // ref.null — push a sentinel; store will treat as None
                                            func_indices.push(u32::MAX);
                                        }
                                    }
                                }
                            }
                            elements.push(ElemSegment {
                                table_idx,
                                offset,
                                func_indices,
                            });
                        }
                    }
                }
                Payload::StartSection { func, .. } => {
                    start = Some(func);
                }
                Payload::ExportSection(reader) => {
                    for export in reader {
                        let export = export.map_err(|e| format!("export error: {e}"))?;
                        let kind = match export.kind {
                            wasmparser::ExternalKind::Func => ExportKind::Func,
                            wasmparser::ExternalKind::Memory => ExportKind::Memory,
                            wasmparser::ExternalKind::Global => ExportKind::Global,
                            wasmparser::ExternalKind::Table => ExportKind::Table,
                            _ => continue,
                        };
                        exports.push(Export {
                            name: export.name.to_string(),
                            kind,
                            index: export.index,
                        });
                    }
                }
                Payload::DataSection(reader) => {
                    for data in reader {
                        let data = data.map_err(|e| format!("data error: {e}"))?;
                        if let wasmparser::DataKind::Active {
                            memory_index: 0,
                            offset_expr,
                        } = data.kind
                        {
                            let offset = decode_const_expr(&offset_expr)?;
                            data_segments.push(DataSegment {
                                offset,
                                data: data.data.to_vec(),
                            });
                        }
                    }
                }
                Payload::CodeSectionEntry(body) => {
                    let mut locals = Vec::new();
                    // First: the params from the function type
                    let type_idx = func_types[num_func_imports as usize + code_idx as usize];
                    let func_type = &types[type_idx as usize];
                    for &param_ty in func_type.params() {
                        locals.push(param_ty);
                    }
                    // Then: the declared locals
                    let local_reader = body.get_locals_reader()
                        .map_err(|e| format!("locals error: {e}"))?;
                    for local in local_reader {
                        let (count, ty) = local.map_err(|e| format!("local error: {e}"))?;
                        for _ in 0..count {
                            locals.push(ty);
                        }
                    }

                    let ops_reader = body.get_operators_reader()
                        .map_err(|e| format!("ops error: {e}"))?;
                    let mut instructions = Vec::new();
                    for op in ops_reader {
                        let op = op.map_err(|e| format!("op error: {e}"))?;
                        if let Some(instr) = decode_op(&op) {
                            instructions.push(instr);
                        }
                    }

                    resolve_block_targets(&mut instructions);
                    func_bodies.push((locals, instructions));
                    code_idx += 1;
                }
                _ => {}
            }
        }

        // Build Func entries — imported funcs occupy indices 0..num_func_imports,
        // code bodies correspond to func_types[num_func_imports..]
        for (i, (locals, mut instr_body)) in func_bodies.into_iter().enumerate() {
            let type_idx = func_types[num_func_imports as usize + i];
            Self::peephole_optimize(&mut instr_body);
            let (body, br_tables) = compile_body(&instr_body, &types);
            funcs.push(Func {
                type_idx,
                locals,
                body,
                br_tables,
            });
        }

        Ok(Module {
            types,
            funcs,
            memories,
            globals,
            exports,
            data_segments,
            tables,
            elements,
            start,
            func_types,
            num_func_imports,
            num_global_imports,
            num_memory_imports,
            num_table_imports,
            imports,
        })
    }

    /// Peephole optimization pass: fuse common instruction sequences into superinstructions.
    /// Replaces consumed instructions with Nop to preserve body length and all PC offsets.
    fn peephole_optimize(body: &mut [Instruction]) {
        let len = body.len();
        let mut i = 0;
        while i + 1 < len {
            match (&body[i], &body[i + 1]) {
                // LocalGet + I32Const → LocalGetI32Const
                (Instruction::LocalGet(idx), Instruction::I32Const(val)) => {
                    let idx = *idx;
                    let val = *val;
                    body[i] = Instruction::LocalGetI32Const(idx, val);
                    body[i + 1] = Instruction::Nop;
                    i += 2;
                }
                // LocalGet + LocalGet → LocalGetLocalGet
                (Instruction::LocalGet(a), Instruction::LocalGet(b)) => {
                    let a = *a;
                    let b = *b;
                    body[i] = Instruction::LocalGetLocalGet(a, b);
                    body[i + 1] = Instruction::Nop;
                    i += 2;
                }
                _ => {
                    i += 1;
                }
            }
        }
    }

    /// Get a local function by global index (accounting for imports).
    pub fn get_func(&self, idx: u32) -> Option<&Func> {
        if idx < self.num_func_imports {
            None // imported function — not in self.funcs
        } else {
            self.funcs.get((idx - self.num_func_imports) as usize)
        }
    }

    /// Check if a function index refers to an import.
    pub fn is_import(&self, func_idx: u32) -> bool {
        func_idx < self.num_func_imports
    }

    pub fn export_func(&self, name: &str) -> Option<u32> {
        self.exports.iter().find_map(|e| {
            if e.name == name {
                if let ExportKind::Func = e.kind {
                    return Some(e.index);
                }
            }
            None
        })
    }
}

fn decode_const_expr_multi(expr: &wasmparser::ConstExpr) -> Result<Vec<Instruction>, String> {
    let mut reader = expr.get_operators_reader();
    let mut instrs = Vec::new();
    loop {
        let op = reader.read().map_err(|e| format!("const expr error: {e}"))?;
        match op {
            Operator::End => break,
            _ => {
                if let Some(instr) = decode_op(&op) {
                    instrs.push(instr);
                } else {
                    return Err(format!("unsupported const expr op: {op:?}"));
                }
            }
        }
    }
    Ok(instrs)
}

fn decode_const_expr(expr: &wasmparser::ConstExpr) -> Result<Instruction, String> {
    let mut reader = expr.get_operators_reader();
    let op = reader.read().map_err(|e| format!("const expr error: {e}"))?;
    decode_op(&op).ok_or_else(|| format!("unsupported const expr: {op:?}"))
}

fn decode_op(op: &Operator) -> Option<Instruction> {
    Some(match *op {
        Operator::Unreachable => Instruction::Unreachable,
        Operator::Nop => Instruction::Nop,
        Operator::Block { blockty } => Instruction::Block { ty: decode_block_type(blockty), end_pc: 0 },
        Operator::Loop { blockty } => Instruction::Loop { ty: decode_block_type(blockty) },
        Operator::If { blockty } => Instruction::If { ty: decode_block_type(blockty), end_pc: 0, else_pc: None },
        Operator::Else => Instruction::Else,
        Operator::End => Instruction::End,
        Operator::Br { relative_depth } => Instruction::Br(relative_depth),
        Operator::BrIf { relative_depth } => Instruction::BrIf(relative_depth),
        Operator::BrTable { ref targets } => Instruction::BrTable {
            targets: targets.targets().collect::<Result<Vec<_>, _>>().ok()?,
            default: targets.default(),
        },
        Operator::Return => Instruction::Return,
        Operator::Call { function_index } => Instruction::Call(function_index),
        Operator::CallIndirect { type_index, table_index } => Instruction::CallIndirect {
            type_idx: type_index,
            table_idx: table_index,
        },
        Operator::Drop => Instruction::Drop,
        Operator::Select => Instruction::Select,
        Operator::TypedSelect { .. } => Instruction::Select,

        Operator::LocalGet { local_index } => Instruction::LocalGet(local_index),
        Operator::LocalSet { local_index } => Instruction::LocalSet(local_index),
        Operator::LocalTee { local_index } => Instruction::LocalTee(local_index),
        Operator::GlobalGet { global_index } => Instruction::GlobalGet(global_index),
        Operator::GlobalSet { global_index } => Instruction::GlobalSet(global_index),

        Operator::I32Load { memarg } => Instruction::I32Load(memarg.offset),
        Operator::I64Load { memarg } => Instruction::I64Load(memarg.offset),
        Operator::F32Load { memarg } => Instruction::F32Load(memarg.offset),
        Operator::F64Load { memarg } => Instruction::F64Load(memarg.offset),
        Operator::I32Load8S { memarg } => Instruction::I32Load8S(memarg.offset),
        Operator::I32Load8U { memarg } => Instruction::I32Load8U(memarg.offset),
        Operator::I32Load16S { memarg } => Instruction::I32Load16S(memarg.offset),
        Operator::I32Load16U { memarg } => Instruction::I32Load16U(memarg.offset),
        Operator::I64Load8S { memarg } => Instruction::I64Load8S(memarg.offset),
        Operator::I64Load8U { memarg } => Instruction::I64Load8U(memarg.offset),
        Operator::I64Load16S { memarg } => Instruction::I64Load16S(memarg.offset),
        Operator::I64Load16U { memarg } => Instruction::I64Load16U(memarg.offset),
        Operator::I64Load32S { memarg } => Instruction::I64Load32S(memarg.offset),
        Operator::I64Load32U { memarg } => Instruction::I64Load32U(memarg.offset),
        Operator::I32Store { memarg } => Instruction::I32Store(memarg.offset),
        Operator::I64Store { memarg } => Instruction::I64Store(memarg.offset),
        Operator::F32Store { memarg } => Instruction::F32Store(memarg.offset),
        Operator::F64Store { memarg } => Instruction::F64Store(memarg.offset),
        Operator::I32Store8 { memarg } => Instruction::I32Store8(memarg.offset),
        Operator::I32Store16 { memarg } => Instruction::I32Store16(memarg.offset),
        Operator::I64Store8 { memarg } => Instruction::I64Store8(memarg.offset),
        Operator::I64Store16 { memarg } => Instruction::I64Store16(memarg.offset),
        Operator::I64Store32 { memarg } => Instruction::I64Store32(memarg.offset),
        Operator::MemorySize { .. } => Instruction::MemorySize,
        Operator::MemoryGrow { .. } => Instruction::MemoryGrow,

        Operator::I32Const { value } => Instruction::I32Const(value),
        Operator::I64Const { value } => Instruction::I64Const(value),
        Operator::F32Const { value } => Instruction::F32Const(f32::from_bits(value.bits())),
        Operator::F64Const { value } => Instruction::F64Const(f64::from_bits(value.bits())),

        Operator::I32Eqz => Instruction::I32Eqz,
        Operator::I32Eq => Instruction::I32Eq,
        Operator::I32Ne => Instruction::I32Ne,
        Operator::I32LtS => Instruction::I32LtS,
        Operator::I32LtU => Instruction::I32LtU,
        Operator::I32GtS => Instruction::I32GtS,
        Operator::I32GtU => Instruction::I32GtU,
        Operator::I32LeS => Instruction::I32LeS,
        Operator::I32LeU => Instruction::I32LeU,
        Operator::I32GeS => Instruction::I32GeS,
        Operator::I32GeU => Instruction::I32GeU,
        Operator::I32Clz => Instruction::I32Clz,
        Operator::I32Ctz => Instruction::I32Ctz,
        Operator::I32Popcnt => Instruction::I32Popcnt,
        Operator::I32Add => Instruction::I32Add,
        Operator::I32Sub => Instruction::I32Sub,
        Operator::I32Mul => Instruction::I32Mul,
        Operator::I32DivS => Instruction::I32DivS,
        Operator::I32DivU => Instruction::I32DivU,
        Operator::I32RemS => Instruction::I32RemS,
        Operator::I32RemU => Instruction::I32RemU,
        Operator::I32And => Instruction::I32And,
        Operator::I32Or => Instruction::I32Or,
        Operator::I32Xor => Instruction::I32Xor,
        Operator::I32Shl => Instruction::I32Shl,
        Operator::I32ShrS => Instruction::I32ShrS,
        Operator::I32ShrU => Instruction::I32ShrU,
        Operator::I32Rotl => Instruction::I32Rotl,
        Operator::I32Rotr => Instruction::I32Rotr,

        Operator::I64Eqz => Instruction::I64Eqz,
        Operator::I64Eq => Instruction::I64Eq,
        Operator::I64Ne => Instruction::I64Ne,
        Operator::I64LtS => Instruction::I64LtS,
        Operator::I64LtU => Instruction::I64LtU,
        Operator::I64GtS => Instruction::I64GtS,
        Operator::I64GtU => Instruction::I64GtU,
        Operator::I64LeS => Instruction::I64LeS,
        Operator::I64LeU => Instruction::I64LeU,
        Operator::I64GeS => Instruction::I64GeS,
        Operator::I64GeU => Instruction::I64GeU,
        Operator::I64Clz => Instruction::I64Clz,
        Operator::I64Ctz => Instruction::I64Ctz,
        Operator::I64Popcnt => Instruction::I64Popcnt,
        Operator::I64Add => Instruction::I64Add,
        Operator::I64Sub => Instruction::I64Sub,
        Operator::I64Mul => Instruction::I64Mul,
        Operator::I64DivS => Instruction::I64DivS,
        Operator::I64DivU => Instruction::I64DivU,
        Operator::I64RemS => Instruction::I64RemS,
        Operator::I64RemU => Instruction::I64RemU,
        Operator::I64And => Instruction::I64And,
        Operator::I64Or => Instruction::I64Or,
        Operator::I64Xor => Instruction::I64Xor,
        Operator::I64Shl => Instruction::I64Shl,
        Operator::I64ShrS => Instruction::I64ShrS,
        Operator::I64ShrU => Instruction::I64ShrU,
        Operator::I64Rotl => Instruction::I64Rotl,
        Operator::I64Rotr => Instruction::I64Rotr,

        Operator::I32WrapI64 => Instruction::I32WrapI64,
        Operator::I64ExtendI32S => Instruction::I64ExtendI32S,
        Operator::I64ExtendI32U => Instruction::I64ExtendI32U,

        Operator::F32Eq => Instruction::F32Eq,
        Operator::F32Ne => Instruction::F32Ne,
        Operator::F32Lt => Instruction::F32Lt,
        Operator::F32Gt => Instruction::F32Gt,
        Operator::F32Le => Instruction::F32Le,
        Operator::F32Ge => Instruction::F32Ge,
        Operator::F64Eq => Instruction::F64Eq,
        Operator::F64Ne => Instruction::F64Ne,
        Operator::F64Lt => Instruction::F64Lt,
        Operator::F64Gt => Instruction::F64Gt,
        Operator::F64Le => Instruction::F64Le,
        Operator::F64Ge => Instruction::F64Ge,
        Operator::F32Abs => Instruction::F32Abs,
        Operator::F32Neg => Instruction::F32Neg,
        Operator::F32Ceil => Instruction::F32Ceil,
        Operator::F32Floor => Instruction::F32Floor,
        Operator::F32Trunc => Instruction::F32Trunc,
        Operator::F32Nearest => Instruction::F32Nearest,
        Operator::F32Sqrt => Instruction::F32Sqrt,
        Operator::F32Add => Instruction::F32Add,
        Operator::F32Sub => Instruction::F32Sub,
        Operator::F32Mul => Instruction::F32Mul,
        Operator::F32Div => Instruction::F32Div,
        Operator::F32Min => Instruction::F32Min,
        Operator::F32Max => Instruction::F32Max,
        Operator::F32Copysign => Instruction::F32Copysign,
        Operator::F64Abs => Instruction::F64Abs,
        Operator::F64Neg => Instruction::F64Neg,
        Operator::F64Ceil => Instruction::F64Ceil,
        Operator::F64Floor => Instruction::F64Floor,
        Operator::F64Trunc => Instruction::F64Trunc,
        Operator::F64Nearest => Instruction::F64Nearest,
        Operator::F64Sqrt => Instruction::F64Sqrt,
        Operator::F64Add => Instruction::F64Add,
        Operator::F64Sub => Instruction::F64Sub,
        Operator::F64Mul => Instruction::F64Mul,
        Operator::F64Div => Instruction::F64Div,
        Operator::F64Min => Instruction::F64Min,
        Operator::F64Max => Instruction::F64Max,
        Operator::F64Copysign => Instruction::F64Copysign,

        Operator::I32TruncF32S => Instruction::I32TruncF32S,
        Operator::I32TruncF32U => Instruction::I32TruncF32U,
        Operator::I32TruncF64S => Instruction::I32TruncF64S,
        Operator::I32TruncF64U => Instruction::I32TruncF64U,
        Operator::I64TruncF32S => Instruction::I64TruncF32S,
        Operator::I64TruncF32U => Instruction::I64TruncF32U,
        Operator::I64TruncF64S => Instruction::I64TruncF64S,
        Operator::I64TruncF64U => Instruction::I64TruncF64U,
        Operator::F32ConvertI32S => Instruction::F32ConvertI32S,
        Operator::F32ConvertI32U => Instruction::F32ConvertI32U,
        Operator::F32ConvertI64S => Instruction::F32ConvertI64S,
        Operator::F32ConvertI64U => Instruction::F32ConvertI64U,
        Operator::F32DemoteF64 => Instruction::F32DemoteF64,
        Operator::F64ConvertI32S => Instruction::F64ConvertI32S,
        Operator::F64ConvertI32U => Instruction::F64ConvertI32U,
        Operator::F64ConvertI64S => Instruction::F64ConvertI64S,
        Operator::F64ConvertI64U => Instruction::F64ConvertI64U,
        Operator::F64PromoteF32 => Instruction::F64PromoteF32,
        Operator::I32ReinterpretF32 => Instruction::I32ReinterpretF32,
        Operator::I64ReinterpretF64 => Instruction::I64ReinterpretF64,
        Operator::F32ReinterpretI32 => Instruction::F32ReinterpretI32,
        Operator::F64ReinterpretI64 => Instruction::F64ReinterpretI64,

        Operator::I32Extend8S => Instruction::I32Extend8S,
        Operator::I32Extend16S => Instruction::I32Extend16S,
        Operator::I64Extend8S => Instruction::I64Extend8S,
        Operator::I64Extend16S => Instruction::I64Extend16S,
        Operator::I64Extend32S => Instruction::I64Extend32S,

        Operator::I32TruncSatF32S => Instruction::I32TruncSatF32S,
        Operator::I32TruncSatF32U => Instruction::I32TruncSatF32U,
        Operator::I32TruncSatF64S => Instruction::I32TruncSatF64S,
        Operator::I32TruncSatF64U => Instruction::I32TruncSatF64U,
        Operator::I64TruncSatF32S => Instruction::I64TruncSatF32S,
        Operator::I64TruncSatF32U => Instruction::I64TruncSatF32U,
        Operator::I64TruncSatF64S => Instruction::I64TruncSatF64S,
        Operator::I64TruncSatF64U => Instruction::I64TruncSatF64U,

        Operator::TableInit { elem_index, table } => Instruction::TableInit { elem_idx: elem_index, table_idx: table },
        Operator::ElemDrop { elem_index } => Instruction::ElemDrop(elem_index),

        _ => return None,
    })
}

fn decode_block_type(bt: wasmparser::BlockType) -> BlockType {
    match bt {
        wasmparser::BlockType::Empty => BlockType::Empty,
        wasmparser::BlockType::Type(ty) => BlockType::Val(ty),
        wasmparser::BlockType::FuncType(idx) => BlockType::FuncType(idx),
    }
}

/// Fill in end_pc/else_pc for Block and If instructions.
fn resolve_block_targets(body: &mut [Instruction]) {
    // Stack of (block_start_pc, is_if)
    let mut stack: Vec<(usize, bool)> = Vec::new();
    let mut else_map: Vec<(usize, usize)> = Vec::new(); // (if_pc, else_pc)

    for i in 0..body.len() {
        match &body[i] {
            Instruction::Block { .. } => stack.push((i, false)),
            Instruction::Loop { .. } => stack.push((i, false)),
            Instruction::If { .. } => stack.push((i, true)),
            Instruction::Else => {
                // Record the else position for the most recent If
                if let Some(&(if_pc, true)) = stack.last() {
                    else_map.push((if_pc, i));
                }
            }
            Instruction::End => {
                if let Some((start_pc, is_if)) = stack.pop() {
                    match &body[start_pc] {
                        Instruction::Block { .. } | Instruction::If { .. } => {
                            let else_pc = if is_if {
                                else_map.iter().rev()
                                    .find(|(ip, _)| *ip == start_pc)
                                    .map(|(_, ep)| *ep)
                            } else {
                                None
                            };
                            // Patch the instruction
                            match &mut body[start_pc] {
                                Instruction::Block { end_pc, .. } => *end_pc = i,
                                Instruction::If { end_pc, else_pc: ep, .. } => {
                                    *end_pc = i;
                                    *ep = else_pc;
                                }
                                _ => {}
                            }
                        }
                        _ => {} // Loop doesn't need end_pc
                    }
                }
            }
            _ => {}
        }
    }
}
