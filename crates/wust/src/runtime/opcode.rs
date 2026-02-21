use wasmparser::{FuncType, Operator};

/// Compile-time metadata for a block/loop/if control structure.
///
/// All fields are resolved at compile time — the interpreter just looks them up
/// by block index, no runtime block frame tracking needed.
#[derive(Debug, Clone)]
pub struct BlockDef {
    pub kind: BlockKind,
    /// Number of result values produced by this block (preserved on forward br).
    pub result_arity: u32,
    /// Number of param values consumed by this block (preserved on backward br to loops).
    pub param_arity: u32,
    /// PC to jump to on `br` to this block.
    /// Blocks/If: end_pc + 1 (past the END). Loops: start_pc + 1 (first op in body).
    pub br_target: u32,
    /// PC of the END instruction.
    pub end_pc: u32,
    /// PC of the ELSE instruction (0 if no else clause).
    pub else_pc: u32,
    /// Operand stack depth (relative to operand_base) at block entry, BELOW
    /// block params. This is a compile-time constant — WASM validation
    /// guarantees stack depth is statically known at every instruction.
    pub entry_depth: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlockKind {
    Block,
    Loop,
    If,
}

/// Out-of-line branch table data for OP_BR_TABLE.
#[derive(Debug, Clone)]
pub struct BrTable {
    /// Target block indices for each table entry.
    pub targets: Box<[u32]>,
    /// Default target block index.
    pub default: u32,
}

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
// Superinstructions (defined but not currently emitted)
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

/// Compute block result arity from a wasmparser BlockType.
fn block_result_arity(bt: wasmparser::BlockType, types: &[FuncType]) -> u32 {
    match bt {
        wasmparser::BlockType::Empty => 0,
        wasmparser::BlockType::Type(_) => 1,
        wasmparser::BlockType::FuncType(idx) => types[idx as usize].results().len() as u32,
    }
}

/// Compute block param arity from a wasmparser BlockType.
fn block_param_arity(bt: wasmparser::BlockType, types: &[FuncType]) -> u32 {
    match bt {
        wasmparser::BlockType::Empty | wasmparser::BlockType::Type(_) => 0,
        wasmparser::BlockType::FuncType(idx) => types[idx as usize].params().len() as u32,
    }
}

/// Convert a single wasmparser Operator into an Op. Block/Loop/If ops create
/// BlockDef entries. Br ops store relative depth (resolved to block_idx in
/// pass 2). Returns None for unsupported operators.
fn decode_operator(
    op: &Operator,
    pc: u32,
    types: &[FuncType],
    br_tables: &mut Vec<(Vec<u32>, u32)>,
    blocks: &mut Vec<BlockDef>,
) -> Option<Op> {
    Some(match *op {
        Operator::Unreachable => Op::unit(OP_UNREACHABLE),
        Operator::Nop => Op::unit(OP_NOP),
        Operator::Block { blockty } => {
            let block_idx = blocks.len() as u32;
            blocks.push(BlockDef {
                kind: BlockKind::Block,
                result_arity: block_result_arity(blockty, types),
                param_arity: block_param_arity(blockty, types),
                br_target: 0,
                end_pc: 0,
                else_pc: 0,
                entry_depth: 0,
            });
            Op::new(OP_BLOCK, block_idx as u64)
        }
        Operator::Loop { blockty } => {
            let block_idx = blocks.len() as u32;
            blocks.push(BlockDef {
                kind: BlockKind::Loop,
                result_arity: block_result_arity(blockty, types),
                param_arity: block_param_arity(blockty, types),
                br_target: 0,
                end_pc: 0,
                else_pc: 0,
                entry_depth: 0,
            });
            Op::new(OP_LOOP, block_idx as u64)
        }
        Operator::If { blockty } => {
            let block_idx = blocks.len() as u32;
            blocks.push(BlockDef {
                kind: BlockKind::If,
                result_arity: block_result_arity(blockty, types),
                param_arity: block_param_arity(blockty, types),
                br_target: 0,
                end_pc: 0,
                else_pc: 0,
                entry_depth: 0,
            });
            Op::new(OP_IF, block_idx as u64)
        }
        Operator::Else => Op::unit(OP_ELSE),
        Operator::End => Op::unit(OP_END),
        // br/br_if store relative depth in pass 1; resolved to block_idx in pass 2
        Operator::Br { relative_depth } => Op::new(OP_BR, relative_depth as u64),
        Operator::BrIf { relative_depth } => Op::new(OP_BR_IF, relative_depth as u64),
        Operator::BrTable { ref targets } => {
            let target_list: Vec<u32> = targets.targets().collect::<Result<Vec<_>, _>>().ok()?;
            let default = targets.default();
            let idx = br_tables.len();
            br_tables.push((target_list, default));
            Op::new(OP_BR_TABLE, idx as u64)
        }
        Operator::Return => Op::unit(OP_RETURN),
        Operator::Call { function_index } => Op::new(OP_CALL, function_index as u64),
        Operator::CallIndirect {
            type_index,
            table_index,
        } => Op::pair(OP_CALL_INDIRECT, type_index as u32, table_index as u32),
        Operator::Drop => Op::unit(OP_DROP),
        Operator::Select => Op::unit(OP_SELECT),
        Operator::TypedSelect { .. } => Op::unit(OP_SELECT),

        Operator::LocalGet { local_index } => Op::new(OP_LOCAL_GET, local_index as u64),
        Operator::LocalSet { local_index } => Op::new(OP_LOCAL_SET, local_index as u64),
        Operator::LocalTee { local_index } => Op::new(OP_LOCAL_TEE, local_index as u64),
        Operator::GlobalGet { global_index } => Op::new(OP_GLOBAL_GET, global_index as u64),
        Operator::GlobalSet { global_index } => Op::new(OP_GLOBAL_SET, global_index as u64),

        Operator::I32Load { memarg } => Op::new(OP_I32_LOAD, memarg.offset),
        Operator::I64Load { memarg } => Op::new(OP_I64_LOAD, memarg.offset),
        Operator::F32Load { memarg } => Op::new(OP_F32_LOAD, memarg.offset),
        Operator::F64Load { memarg } => Op::new(OP_F64_LOAD, memarg.offset),
        Operator::I32Load8S { memarg } => Op::new(OP_I32_LOAD8_S, memarg.offset),
        Operator::I32Load8U { memarg } => Op::new(OP_I32_LOAD8_U, memarg.offset),
        Operator::I32Load16S { memarg } => Op::new(OP_I32_LOAD16_S, memarg.offset),
        Operator::I32Load16U { memarg } => Op::new(OP_I32_LOAD16_U, memarg.offset),
        Operator::I64Load8S { memarg } => Op::new(OP_I64_LOAD8_S, memarg.offset),
        Operator::I64Load8U { memarg } => Op::new(OP_I64_LOAD8_U, memarg.offset),
        Operator::I64Load16S { memarg } => Op::new(OP_I64_LOAD16_S, memarg.offset),
        Operator::I64Load16U { memarg } => Op::new(OP_I64_LOAD16_U, memarg.offset),
        Operator::I64Load32S { memarg } => Op::new(OP_I64_LOAD32_S, memarg.offset),
        Operator::I64Load32U { memarg } => Op::new(OP_I64_LOAD32_U, memarg.offset),
        Operator::I32Store { memarg } => Op::new(OP_I32_STORE, memarg.offset),
        Operator::I64Store { memarg } => Op::new(OP_I64_STORE, memarg.offset),
        Operator::F32Store { memarg } => Op::new(OP_F32_STORE, memarg.offset),
        Operator::F64Store { memarg } => Op::new(OP_F64_STORE, memarg.offset),
        Operator::I32Store8 { memarg } => Op::new(OP_I32_STORE8, memarg.offset),
        Operator::I32Store16 { memarg } => Op::new(OP_I32_STORE16, memarg.offset),
        Operator::I64Store8 { memarg } => Op::new(OP_I64_STORE8, memarg.offset),
        Operator::I64Store16 { memarg } => Op::new(OP_I64_STORE16, memarg.offset),
        Operator::I64Store32 { memarg } => Op::new(OP_I64_STORE32, memarg.offset),
        Operator::MemorySize { .. } => Op::unit(OP_MEMORY_SIZE),
        Operator::MemoryGrow { .. } => Op::unit(OP_MEMORY_GROW),

        Operator::I32Const { value } => Op::new(OP_I32_CONST, value as u32 as u64),
        Operator::I64Const { value } => Op::new(OP_I64_CONST, value as u64),
        Operator::F32Const { value } => Op::new(OP_F32_CONST, value.bits() as u64),
        Operator::F64Const { value } => Op::new(OP_F64_CONST, value.bits()),

        Operator::I32Eqz => Op::unit(OP_I32_EQZ),
        Operator::I32Eq => Op::unit(OP_I32_EQ),
        Operator::I32Ne => Op::unit(OP_I32_NE),
        Operator::I32LtS => Op::unit(OP_I32_LT_S),
        Operator::I32LtU => Op::unit(OP_I32_LT_U),
        Operator::I32GtS => Op::unit(OP_I32_GT_S),
        Operator::I32GtU => Op::unit(OP_I32_GT_U),
        Operator::I32LeS => Op::unit(OP_I32_LE_S),
        Operator::I32LeU => Op::unit(OP_I32_LE_U),
        Operator::I32GeS => Op::unit(OP_I32_GE_S),
        Operator::I32GeU => Op::unit(OP_I32_GE_U),
        Operator::I32Clz => Op::unit(OP_I32_CLZ),
        Operator::I32Ctz => Op::unit(OP_I32_CTZ),
        Operator::I32Popcnt => Op::unit(OP_I32_POPCNT),
        Operator::I32Add => Op::unit(OP_I32_ADD),
        Operator::I32Sub => Op::unit(OP_I32_SUB),
        Operator::I32Mul => Op::unit(OP_I32_MUL),
        Operator::I32DivS => Op::unit(OP_I32_DIV_S),
        Operator::I32DivU => Op::unit(OP_I32_DIV_U),
        Operator::I32RemS => Op::unit(OP_I32_REM_S),
        Operator::I32RemU => Op::unit(OP_I32_REM_U),
        Operator::I32And => Op::unit(OP_I32_AND),
        Operator::I32Or => Op::unit(OP_I32_OR),
        Operator::I32Xor => Op::unit(OP_I32_XOR),
        Operator::I32Shl => Op::unit(OP_I32_SHL),
        Operator::I32ShrS => Op::unit(OP_I32_SHR_S),
        Operator::I32ShrU => Op::unit(OP_I32_SHR_U),
        Operator::I32Rotl => Op::unit(OP_I32_ROTL),
        Operator::I32Rotr => Op::unit(OP_I32_ROTR),

        Operator::I64Eqz => Op::unit(OP_I64_EQZ),
        Operator::I64Eq => Op::unit(OP_I64_EQ),
        Operator::I64Ne => Op::unit(OP_I64_NE),
        Operator::I64LtS => Op::unit(OP_I64_LT_S),
        Operator::I64LtU => Op::unit(OP_I64_LT_U),
        Operator::I64GtS => Op::unit(OP_I64_GT_S),
        Operator::I64GtU => Op::unit(OP_I64_GT_U),
        Operator::I64LeS => Op::unit(OP_I64_LE_S),
        Operator::I64LeU => Op::unit(OP_I64_LE_U),
        Operator::I64GeS => Op::unit(OP_I64_GE_S),
        Operator::I64GeU => Op::unit(OP_I64_GE_U),
        Operator::I64Clz => Op::unit(OP_I64_CLZ),
        Operator::I64Ctz => Op::unit(OP_I64_CTZ),
        Operator::I64Popcnt => Op::unit(OP_I64_POPCNT),
        Operator::I64Add => Op::unit(OP_I64_ADD),
        Operator::I64Sub => Op::unit(OP_I64_SUB),
        Operator::I64Mul => Op::unit(OP_I64_MUL),
        Operator::I64DivS => Op::unit(OP_I64_DIV_S),
        Operator::I64DivU => Op::unit(OP_I64_DIV_U),
        Operator::I64RemS => Op::unit(OP_I64_REM_S),
        Operator::I64RemU => Op::unit(OP_I64_REM_U),
        Operator::I64And => Op::unit(OP_I64_AND),
        Operator::I64Or => Op::unit(OP_I64_OR),
        Operator::I64Xor => Op::unit(OP_I64_XOR),
        Operator::I64Shl => Op::unit(OP_I64_SHL),
        Operator::I64ShrS => Op::unit(OP_I64_SHR_S),
        Operator::I64ShrU => Op::unit(OP_I64_SHR_U),
        Operator::I64Rotl => Op::unit(OP_I64_ROTL),
        Operator::I64Rotr => Op::unit(OP_I64_ROTR),

        Operator::I32WrapI64 => Op::unit(OP_I32_WRAP_I64),
        Operator::I64ExtendI32S => Op::unit(OP_I64_EXTEND_I32_S),
        Operator::I64ExtendI32U => Op::unit(OP_I64_EXTEND_I32_U),

        Operator::F32Eq => Op::unit(OP_F32_EQ),
        Operator::F32Ne => Op::unit(OP_F32_NE),
        Operator::F32Lt => Op::unit(OP_F32_LT),
        Operator::F32Gt => Op::unit(OP_F32_GT),
        Operator::F32Le => Op::unit(OP_F32_LE),
        Operator::F32Ge => Op::unit(OP_F32_GE),
        Operator::F64Eq => Op::unit(OP_F64_EQ),
        Operator::F64Ne => Op::unit(OP_F64_NE),
        Operator::F64Lt => Op::unit(OP_F64_LT),
        Operator::F64Gt => Op::unit(OP_F64_GT),
        Operator::F64Le => Op::unit(OP_F64_LE),
        Operator::F64Ge => Op::unit(OP_F64_GE),
        Operator::F32Abs => Op::unit(OP_F32_ABS),
        Operator::F32Neg => Op::unit(OP_F32_NEG),
        Operator::F32Ceil => Op::unit(OP_F32_CEIL),
        Operator::F32Floor => Op::unit(OP_F32_FLOOR),
        Operator::F32Trunc => Op::unit(OP_F32_TRUNC),
        Operator::F32Nearest => Op::unit(OP_F32_NEAREST),
        Operator::F32Sqrt => Op::unit(OP_F32_SQRT),
        Operator::F32Add => Op::unit(OP_F32_ADD),
        Operator::F32Sub => Op::unit(OP_F32_SUB),
        Operator::F32Mul => Op::unit(OP_F32_MUL),
        Operator::F32Div => Op::unit(OP_F32_DIV),
        Operator::F32Min => Op::unit(OP_F32_MIN),
        Operator::F32Max => Op::unit(OP_F32_MAX),
        Operator::F32Copysign => Op::unit(OP_F32_COPYSIGN),
        Operator::F64Abs => Op::unit(OP_F64_ABS),
        Operator::F64Neg => Op::unit(OP_F64_NEG),
        Operator::F64Ceil => Op::unit(OP_F64_CEIL),
        Operator::F64Floor => Op::unit(OP_F64_FLOOR),
        Operator::F64Trunc => Op::unit(OP_F64_TRUNC),
        Operator::F64Nearest => Op::unit(OP_F64_NEAREST),
        Operator::F64Sqrt => Op::unit(OP_F64_SQRT),
        Operator::F64Add => Op::unit(OP_F64_ADD),
        Operator::F64Sub => Op::unit(OP_F64_SUB),
        Operator::F64Mul => Op::unit(OP_F64_MUL),
        Operator::F64Div => Op::unit(OP_F64_DIV),
        Operator::F64Min => Op::unit(OP_F64_MIN),
        Operator::F64Max => Op::unit(OP_F64_MAX),
        Operator::F64Copysign => Op::unit(OP_F64_COPYSIGN),

        Operator::I32TruncF32S => Op::unit(OP_I32_TRUNC_F32_S),
        Operator::I32TruncF32U => Op::unit(OP_I32_TRUNC_F32_U),
        Operator::I32TruncF64S => Op::unit(OP_I32_TRUNC_F64_S),
        Operator::I32TruncF64U => Op::unit(OP_I32_TRUNC_F64_U),
        Operator::I64TruncF32S => Op::unit(OP_I64_TRUNC_F32_S),
        Operator::I64TruncF32U => Op::unit(OP_I64_TRUNC_F32_U),
        Operator::I64TruncF64S => Op::unit(OP_I64_TRUNC_F64_S),
        Operator::I64TruncF64U => Op::unit(OP_I64_TRUNC_F64_U),
        Operator::F32ConvertI32S => Op::unit(OP_F32_CONVERT_I32_S),
        Operator::F32ConvertI32U => Op::unit(OP_F32_CONVERT_I32_U),
        Operator::F32ConvertI64S => Op::unit(OP_F32_CONVERT_I64_S),
        Operator::F32ConvertI64U => Op::unit(OP_F32_CONVERT_I64_U),
        Operator::F32DemoteF64 => Op::unit(OP_F32_DEMOTE_F64),
        Operator::F64ConvertI32S => Op::unit(OP_F64_CONVERT_I32_S),
        Operator::F64ConvertI32U => Op::unit(OP_F64_CONVERT_I32_U),
        Operator::F64ConvertI64S => Op::unit(OP_F64_CONVERT_I64_S),
        Operator::F64ConvertI64U => Op::unit(OP_F64_CONVERT_I64_U),
        Operator::F64PromoteF32 => Op::unit(OP_F64_PROMOTE_F32),
        Operator::I32ReinterpretF32 => Op::unit(OP_I32_REINTERPRET_F32),
        Operator::I64ReinterpretF64 => Op::unit(OP_I64_REINTERPRET_F64),
        Operator::F32ReinterpretI32 => Op::unit(OP_F32_REINTERPRET_I32),
        Operator::F64ReinterpretI64 => Op::unit(OP_F64_REINTERPRET_I64),

        Operator::I32Extend8S => Op::unit(OP_I32_EXTEND8_S),
        Operator::I32Extend16S => Op::unit(OP_I32_EXTEND16_S),
        Operator::I64Extend8S => Op::unit(OP_I64_EXTEND8_S),
        Operator::I64Extend16S => Op::unit(OP_I64_EXTEND16_S),
        Operator::I64Extend32S => Op::unit(OP_I64_EXTEND32_S),

        Operator::I32TruncSatF32S => Op::unit(OP_I32_TRUNC_SAT_F32_S),
        Operator::I32TruncSatF32U => Op::unit(OP_I32_TRUNC_SAT_F32_U),
        Operator::I32TruncSatF64S => Op::unit(OP_I32_TRUNC_SAT_F64_S),
        Operator::I32TruncSatF64U => Op::unit(OP_I32_TRUNC_SAT_F64_U),
        Operator::I64TruncSatF32S => Op::unit(OP_I64_TRUNC_SAT_F32_S),
        Operator::I64TruncSatF32U => Op::unit(OP_I64_TRUNC_SAT_F32_U),
        Operator::I64TruncSatF64S => Op::unit(OP_I64_TRUNC_SAT_F64_S),
        Operator::I64TruncSatF64U => Op::unit(OP_I64_TRUNC_SAT_F64_U),

        Operator::RefFunc { function_index } => Op::new(OP_REF_FUNC, function_index as u64),
        Operator::RefNull { .. } => Op::unit(OP_REF_NULL),
        Operator::RefIsNull => Op::unit(OP_REF_IS_NULL),

        Operator::TableInit { elem_index, table } => Op::pair(OP_TABLE_INIT, elem_index, table),
        Operator::ElemDrop { elem_index } => Op::new(OP_ELEM_DROP, elem_index as u64),
        Operator::MemoryInit { data_index, mem: 0 } => Op::new(OP_MEMORY_INIT, data_index as u64),
        Operator::DataDrop { data_index } => Op::new(OP_DATA_DROP, data_index as u64),
        Operator::MemoryCopy {
            dst_mem: 0,
            src_mem: 0,
        } => Op::unit(OP_MEMORY_COPY),
        Operator::MemoryFill { mem: 0 } => Op::unit(OP_MEMORY_FILL),

        Operator::TableGet { table } => Op::new(OP_TABLE_GET, table as u64),
        Operator::TableSet { table } => Op::new(OP_TABLE_SET, table as u64),
        Operator::TableGrow { table } => Op::new(OP_TABLE_GROW, table as u64),
        Operator::TableSize { table } => Op::new(OP_TABLE_SIZE, table as u64),
        Operator::TableCopy {
            dst_table,
            src_table,
        } => Op::pair(OP_TABLE_COPY, dst_table, src_table),
        Operator::TableFill { table } => Op::new(OP_TABLE_FILL, table as u64),

        _ => return None,
    })
}

/// Net stack effect of an opcode (positive = pushes, negative = pops).
/// Control flow and call ops are handled separately by the resolve pass.
fn stack_delta(code: u16) -> i32 {
    match code {
        // No effect
        OP_NOP | OP_UNREACHABLE | OP_BLOCK | OP_LOOP | OP_END | OP_ELSE
        | OP_BR | OP_BR_IF | OP_BR_TABLE | OP_RETURN => 0,

        // Push 1
        OP_I32_CONST | OP_I64_CONST | OP_F32_CONST | OP_F64_CONST
        | OP_LOCAL_GET | OP_GLOBAL_GET | OP_MEMORY_SIZE
        | OP_REF_FUNC | OP_REF_NULL | OP_TABLE_SIZE => 1,

        // Pop 1
        OP_DROP | OP_LOCAL_SET | OP_GLOBAL_SET => -1,

        // Pop 1, push 1 (net 0): unary ops, conversions, loads
        OP_LOCAL_TEE | OP_MEMORY_GROW | OP_REF_IS_NULL
        | OP_I32_EQZ | OP_I64_EQZ
        | OP_I32_CLZ | OP_I32_CTZ | OP_I32_POPCNT
        | OP_I64_CLZ | OP_I64_CTZ | OP_I64_POPCNT
        | OP_F32_ABS | OP_F32_NEG | OP_F32_CEIL | OP_F32_FLOOR
        | OP_F32_TRUNC | OP_F32_NEAREST | OP_F32_SQRT
        | OP_F64_ABS | OP_F64_NEG | OP_F64_CEIL | OP_F64_FLOOR
        | OP_F64_TRUNC | OP_F64_NEAREST | OP_F64_SQRT
        | OP_I32_WRAP_I64 | OP_I64_EXTEND_I32_S | OP_I64_EXTEND_I32_U
        | OP_I32_EXTEND8_S | OP_I32_EXTEND16_S
        | OP_I64_EXTEND8_S | OP_I64_EXTEND16_S | OP_I64_EXTEND32_S
        | OP_I32_REINTERPRET_F32 | OP_I64_REINTERPRET_F64
        | OP_F32_REINTERPRET_I32 | OP_F64_REINTERPRET_I64
        | OP_I32_TRUNC_F32_S | OP_I32_TRUNC_F32_U
        | OP_I32_TRUNC_F64_S | OP_I32_TRUNC_F64_U
        | OP_I64_TRUNC_F32_S | OP_I64_TRUNC_F32_U
        | OP_I64_TRUNC_F64_S | OP_I64_TRUNC_F64_U
        | OP_I32_TRUNC_SAT_F32_S | OP_I32_TRUNC_SAT_F32_U
        | OP_I32_TRUNC_SAT_F64_S | OP_I32_TRUNC_SAT_F64_U
        | OP_I64_TRUNC_SAT_F32_S | OP_I64_TRUNC_SAT_F32_U
        | OP_I64_TRUNC_SAT_F64_S | OP_I64_TRUNC_SAT_F64_U
        | OP_F32_CONVERT_I32_S | OP_F32_CONVERT_I32_U
        | OP_F32_CONVERT_I64_S | OP_F32_CONVERT_I64_U
        | OP_F32_DEMOTE_F64
        | OP_F64_CONVERT_I32_S | OP_F64_CONVERT_I32_U
        | OP_F64_CONVERT_I64_S | OP_F64_CONVERT_I64_U
        | OP_F64_PROMOTE_F32
        | OP_I32_LOAD | OP_I64_LOAD | OP_F32_LOAD | OP_F64_LOAD
        | OP_I32_LOAD8_S | OP_I32_LOAD8_U | OP_I32_LOAD16_S | OP_I32_LOAD16_U
        | OP_I64_LOAD8_S | OP_I64_LOAD8_U | OP_I64_LOAD16_S | OP_I64_LOAD16_U
        | OP_I64_LOAD32_S | OP_I64_LOAD32_U
        | OP_TABLE_GET => 0,

        // Pop 2, push 1 (net -1): binary ops, comparisons, table.grow
        OP_I32_ADD | OP_I32_SUB | OP_I32_MUL | OP_I32_DIV_S | OP_I32_DIV_U
        | OP_I32_REM_S | OP_I32_REM_U
        | OP_I32_AND | OP_I32_OR | OP_I32_XOR
        | OP_I32_SHL | OP_I32_SHR_S | OP_I32_SHR_U | OP_I32_ROTL | OP_I32_ROTR
        | OP_I64_ADD | OP_I64_SUB | OP_I64_MUL | OP_I64_DIV_S | OP_I64_DIV_U
        | OP_I64_REM_S | OP_I64_REM_U
        | OP_I64_AND | OP_I64_OR | OP_I64_XOR
        | OP_I64_SHL | OP_I64_SHR_S | OP_I64_SHR_U | OP_I64_ROTL | OP_I64_ROTR
        | OP_I32_EQ | OP_I32_NE | OP_I32_LT_S | OP_I32_LT_U
        | OP_I32_GT_S | OP_I32_GT_U | OP_I32_LE_S | OP_I32_LE_U
        | OP_I32_GE_S | OP_I32_GE_U
        | OP_I64_EQ | OP_I64_NE | OP_I64_LT_S | OP_I64_LT_U
        | OP_I64_GT_S | OP_I64_GT_U | OP_I64_LE_S | OP_I64_LE_U
        | OP_I64_GE_S | OP_I64_GE_U
        | OP_F32_ADD | OP_F32_SUB | OP_F32_MUL | OP_F32_DIV
        | OP_F32_MIN | OP_F32_MAX | OP_F32_COPYSIGN
        | OP_F64_ADD | OP_F64_SUB | OP_F64_MUL | OP_F64_DIV
        | OP_F64_MIN | OP_F64_MAX | OP_F64_COPYSIGN
        | OP_F32_EQ | OP_F32_NE | OP_F32_LT | OP_F32_GT | OP_F32_LE | OP_F32_GE
        | OP_F64_EQ | OP_F64_NE | OP_F64_LT | OP_F64_GT | OP_F64_LE | OP_F64_GE
        | OP_TABLE_GROW => -1,

        // Pop 2 (net -2): stores, table.set
        OP_I32_STORE | OP_I64_STORE | OP_F32_STORE | OP_F64_STORE
        | OP_I32_STORE8 | OP_I32_STORE16
        | OP_I64_STORE8 | OP_I64_STORE16 | OP_I64_STORE32
        | OP_TABLE_SET => -2,

        // Pop 3, push 1 (net -2): select
        OP_SELECT => -2,

        // Pop 3 (net -3): bulk memory/table ops
        OP_MEMORY_COPY | OP_MEMORY_FILL
        | OP_TABLE_COPY | OP_TABLE_FILL
        | OP_TABLE_INIT | OP_MEMORY_INIT => -3,

        // No stack effect
        OP_ELEM_DROP | OP_DATA_DROP => 0,

        // Superinstructions
        OP_LOCAL_GET_I32_CONST => 2,
        OP_LOCAL_GET_LOCAL_GET => 2,

        // Call/call_indirect handled separately
        OP_CALL | OP_CALL_INDIRECT | OP_IF | OP_IF_ELSE => 0,

        _ => 0,
    }
}

/// Second pass: resolve block targets, br depths, and stack depths.
///
/// 1. Patches end_pc, else_pc, br_target on each BlockDef
/// 2. Rewrites OP_IF to OP_IF_ELSE when an else branch exists
/// 3. Resolves OP_BR/OP_BR_IF relative depths to block indices
/// 4. Resolves br_table entries from relative depths to block indices
/// 5. Tracks operand stack depth to set entry_depth on each BlockDef
fn resolve_pass(
    ops: &mut [Op],
    blocks: &mut [BlockDef],
    br_tables: &mut [(Vec<u32>, u32)],
    types: &[FuncType],
    func_types: &[u32],
) {
    // Block stack: entries are block indices. Block 0 (function-level) is always
    // at the bottom. Used to resolve relative br depths to block indices.
    let mut block_stack: Vec<u32> = vec![0];

    // Stack depth tracking (operand stack depth relative to operand_base).
    let mut depth: i32 = 0;
    let mut unreachable = false;

    // Else map: (if_start_pc, else_pc) for if blocks with else branches.
    let mut else_map: Vec<(usize, usize)> = Vec::new();

    for i in 0..ops.len() {
        let code = ops[i].code;

        match code {
            OP_BLOCK | OP_LOOP => {
                let block_idx = ops[i].imm as u32;
                let block = &mut blocks[block_idx as usize];
                // entry_depth = depth below block params
                block.entry_depth = (depth - block.param_arity as i32) as u32;
                block_stack.push(block_idx);
            }
            OP_IF => {
                if !unreachable { depth -= 1; } // pop condition
                let block_idx = ops[i].imm as u32;
                let block = &mut blocks[block_idx as usize];
                block.entry_depth = (depth - block.param_arity as i32) as u32;
                block_stack.push(block_idx);
            }
            OP_ELSE => {
                if let Some(&block_idx) = block_stack.last() {
                    let block = &blocks[block_idx as usize];
                    let start_pc = block_stack.iter().rev()
                        .position(|&b| b == block_idx)
                        .map(|_| {
                            // Find the OP_IF instruction for this block
                            ops.iter().position(|op| {
                                (op.code == OP_IF || op.code == OP_IF_ELSE) && op.imm as u32 == block_idx
                            }).unwrap_or(0)
                        })
                        .unwrap_or(0);
                    else_map.push((start_pc, i));
                    // Reset depth to entry_depth + param_arity for else branch
                    depth = block.entry_depth as i32 + block.param_arity as i32;
                    unreachable = false;
                }
            }
            OP_END => {
                if let Some(block_idx) = block_stack.pop() {
                    let block = &mut blocks[block_idx as usize];
                    block.end_pc = i as u32;

                    // Compute br_target
                    match block.kind {
                        BlockKind::Loop => {
                            // br to loop = jump to first op in loop body
                            block.br_target = block.end_pc; // placeholder
                            // Find the OP_LOOP instruction position
                            for j in 0..ops.len() {
                                if ops[j].code == OP_LOOP && ops[j].imm as u32 == block_idx {
                                    block.br_target = j as u32 + 1;
                                    break;
                                }
                            }
                        }
                        _ => {
                            // br to block/if = jump past the END
                            block.br_target = i as u32 + 1;
                        }
                    }

                    // Handle else for if blocks
                    if block.kind == BlockKind::If {
                        if let Some(&(_, ep)) = else_map.iter().rev()
                            .find(|(sp, _)| {
                                ops.get(*sp).map(|o| o.imm as u32 == block_idx).unwrap_or(false)
                            })
                        {
                            block.else_pc = ep as u32;
                            // Rewrite OP_IF to OP_IF_ELSE
                            for j in 0..ops.len() {
                                if ops[j].code == OP_IF && ops[j].imm as u32 == block_idx {
                                    ops[j].code = OP_IF_ELSE;
                                    break;
                                }
                            }
                        }
                    }

                    // Restore depth after block
                    depth = block.entry_depth as i32 + block.result_arity as i32;
                    unreachable = false;
                }
            }
            OP_BR => {
                // Resolve relative depth to block_idx
                let rel_depth = ops[i].imm as u32;
                let target_idx = block_stack[block_stack.len() - 1 - rel_depth as usize];
                ops[i].imm = target_idx as u64;
                unreachable = true;
            }
            OP_BR_IF => {
                if !unreachable { depth -= 1; } // pop condition
                let rel_depth = ops[i].imm as u32;
                let target_idx = block_stack[block_stack.len() - 1 - rel_depth as usize];
                ops[i].imm = target_idx as u64;
            }
            OP_BR_TABLE => {
                if !unreachable { depth -= 1; } // pop index
                let table_idx = ops[i].imm as usize;
                let (ref mut targets, ref mut default) = br_tables[table_idx];
                // Resolve each target depth to block_idx
                for t in targets.iter_mut() {
                    *t = block_stack[block_stack.len() - 1 - *t as usize];
                }
                *default = block_stack[block_stack.len() - 1 - *default as usize];
                unreachable = true;
            }
            OP_RETURN | OP_UNREACHABLE => {
                unreachable = true;
            }
            OP_CALL => {
                if !unreachable {
                    let func_idx = ops[i].imm as usize;
                    if func_idx < func_types.len() {
                        let type_idx = func_types[func_idx] as usize;
                        if type_idx < types.len() {
                            let ft = &types[type_idx];
                            depth -= ft.params().len() as i32;
                            depth += ft.results().len() as i32;
                        }
                    }
                }
            }
            OP_CALL_INDIRECT => {
                if !unreachable {
                    depth -= 1; // pop table index
                    let type_idx = ops[i].imm_hi() as usize;
                    if type_idx < types.len() {
                        let ft = &types[type_idx];
                        depth -= ft.params().len() as i32;
                        depth += ft.results().len() as i32;
                    }
                }
            }
            _ => {
                if !unreachable {
                    depth += stack_delta(code);
                }
            }
        }
    }
}

/// Compile wasmparser operators into flat Op bytecode with fully resolved
/// block targets and branch indices.
///
/// Returns the compiled FuncDef components:
/// - `body`: flat instruction array
/// - `blocks`: pre-computed metadata for each block/loop/if (block 0 = function-level)
/// - `br_tables`: out-of-line branch table data with resolved block indices
///
/// All branch targets are resolved to block indices. All entry_depth values
/// are set. The interpreter can execute this without any runtime block tracking.
pub fn compile_body(
    ops_reader: wasmparser::OperatorsReader<'_>,
    types: &[FuncType],
    func_types: &[u32],
    result_arity: u32,
) -> Result<(Box<[Op]>, Box<[BlockDef]>, Box<[BrTable]>), String> {
    let mut ops = Vec::new();
    let mut br_tables_raw: Vec<(Vec<u32>, u32)> = Vec::new();

    // Block 0: implicit function-level block.
    let mut blocks = vec![BlockDef {
        kind: BlockKind::Block,
        result_arity,
        param_arity: 0,
        br_target: 0,
        end_pc: 0,
        else_pc: 0,
        entry_depth: 0,
    }];

    for op_result in ops_reader {
        let op = op_result.map_err(|e| format!("op error: {e}"))?;
        let pc = ops.len() as u32;
        if let Some(compiled) = decode_operator(&op, pc, types, &mut br_tables_raw, &mut blocks) {
            ops.push(compiled);
        }
    }

    // Resolve everything in a second pass
    resolve_pass(&mut ops, &mut blocks, &mut br_tables_raw, types, func_types);

    // Block 0's end_pc and br_target: the final END is at ops.len()-1.
    // br to block 0 = return, target past the END = exits the loop.
    if !ops.is_empty() {
        blocks[0].end_pc = (ops.len() - 1) as u32;
        blocks[0].br_target = ops.len() as u32;
    }

    // Convert br_tables to BrTable structs
    let br_tables: Vec<BrTable> = br_tables_raw.into_iter()
        .map(|(targets, default)| BrTable {
            targets: targets.into_boxed_slice(),
            default,
        })
        .collect();

    Ok((ops.into_boxed_slice(), blocks.into_boxed_slice(), br_tables.into_boxed_slice()))
}
