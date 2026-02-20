use wasmparser::{FuncType, Operator};

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
// 4-byte slot typed variants — the compiler emits these instead of the
// untyped versions so the interpreter knows the operand width.
pub const OP_DROP_32: u16 = 203; // drop 4 bytes
pub const OP_DROP_64: u16 = 204; // drop 8 bytes
pub const OP_SELECT_32: u16 = 205; // select between two 4-byte values
pub const OP_SELECT_64: u16 = 206; // select between two 8-byte values
pub const OP_LOCAL_GET_32: u16 = 207; // imm = byte_offset; push 4 bytes
pub const OP_LOCAL_GET_64: u16 = 208; // imm = byte_offset; push 8 bytes
pub const OP_LOCAL_SET_32: u16 = 209; // imm = byte_offset; pop 4 bytes
pub const OP_LOCAL_SET_64: u16 = 210; // imm = byte_offset; pop 8 bytes
pub const OP_LOCAL_TEE_32: u16 = 211; // imm = byte_offset; peek 4 bytes
pub const OP_LOCAL_TEE_64: u16 = 212; // imm = byte_offset; peek 8 bytes

/// Returns the byte size of a value type on the stack (4 for i32/f32, 8 for i64/f64).
fn val_byte_size(ty: ValType) -> u32 {
    match ty {
        ValType::I32 | ValType::F32 | ValType::Ref(_) => 4,
        ValType::I64 | ValType::F64 => 8,
        ValType::V128 => 16,
    }
}

/// Compute block result arity in bytes from a wasmparser BlockType.
fn block_result_arity(bt: wasmparser::BlockType, types: &[FuncType]) -> u32 {
    match bt {
        wasmparser::BlockType::Empty => 0,
        wasmparser::BlockType::Type(ty) => val_byte_size(ty),
        wasmparser::BlockType::FuncType(idx) => types[idx as usize]
            .results()
            .iter()
            .map(|ty| val_byte_size(*ty))
            .sum(),
    }
}

/// Compute loop arity (param bytes) from a wasmparser BlockType.
fn loop_arity(bt: wasmparser::BlockType, types: &[FuncType]) -> u32 {
    match bt {
        wasmparser::BlockType::Empty | wasmparser::BlockType::Type(_) => 0,
        wasmparser::BlockType::FuncType(idx) => types[idx as usize]
            .params()
            .iter()
            .map(|ty| val_byte_size(*ty))
            .sum(),
    }
}

/// Tracks control flow blocks during compilation for type stack management.
struct ControlBlockInfo {
    /// Type stack height at block entry.
    stack_height: usize,
    /// True for loop blocks.
    is_loop: bool,
    /// The block's type signature.
    block_type: wasmparser::BlockType,
    /// True if code is unreachable (after br/return/unreachable).
    unreachable: bool,
}

/// Pre-computed byte offsets for function locals.
pub(crate) struct LocalInfo {
    /// Byte offset of local[i] from locals base.
    pub offsets: Vec<u32>,
    /// Byte size of local[i] (4 or 8).
    pub sizes: Vec<u32>,
    /// Total bytes for all locals.
    pub total_bytes: u32,
}

impl LocalInfo {
    fn from_locals(locals: &[ValType]) -> Self {
        let mut offsets = Vec::with_capacity(locals.len());
        let mut sizes = Vec::with_capacity(locals.len());
        let mut offset: u32 = 0;
        for ty in locals {
            let size = val_byte_size(*ty);
            offsets.push(offset);
            sizes.push(size);
            offset += size;
        }
        Self {
            offsets,
            sizes,
            total_bytes: offset,
        }
    }
}

/// Convert a single wasmparser Operator into an Op, or return None for
/// unsupported operators. Block/If ops are emitted with placeholder targets
/// that get patched by `resolve_block_targets`.
///
/// `type_stack` tracks the value types on the operand stack so we can emit
/// typed variants of DROP and SELECT. `local_info` provides byte offsets
/// for typed LOCAL_GET/SET/TEE opcodes.
fn decode_operator(
    op: &Operator,
    types: &[FuncType],
    br_tables: &mut Vec<(Vec<u32>, u32)>,
    local_info: &LocalInfo,
    type_stack: &mut Vec<ValType>,
    control_stack: &mut Vec<ControlBlockInfo>,
) -> Option<Op> {
    Some(match *op {
        Operator::Unreachable => {
            // Mark as unreachable — stop tracking types until next reachable point
            if let Some(ctrl) = control_stack.last_mut() {
                ctrl.unreachable = true;
            }
            Op::unit(OP_UNREACHABLE)
        }
        Operator::Nop => Op::unit(OP_NOP),
        Operator::Block { blockty } => {
            let arity = block_result_arity(blockty, types);
            let stack_height = type_stack.len();
            control_stack.push(ControlBlockInfo {
                stack_height,
                is_loop: false,
                block_type: blockty,
                unreachable: false,
            });
            // end_pc placeholder = 0, will be patched
            Op::pair(OP_BLOCK, 0, arity)
        }
        Operator::Loop { blockty } => {
            let arity = loop_arity(blockty, types);
            let stack_height = type_stack.len();
            control_stack.push(ControlBlockInfo {
                stack_height,
                is_loop: true,
                block_type: blockty,
                unreachable: false,
            });
            Op::new(OP_LOOP, arity as u64)
        }
        Operator::If { blockty } => {
            type_stack.pop(); // condition
            let arity = block_result_arity(blockty, types);
            let stack_height = type_stack.len();
            control_stack.push(ControlBlockInfo {
                stack_height,
                is_loop: false,
                block_type: blockty,
                unreachable: false,
            });
            // end_pc placeholder = 0, will be patched
            Op::pair(OP_IF, 0, arity)
        }
        Operator::Else => {
            // Reset type stack to block entry height, push block params
            if let Some(ctrl) = control_stack.last_mut() {
                type_stack.truncate(ctrl.stack_height);
                ctrl.unreachable = false;
                // Push block params for else branch
                if let wasmparser::BlockType::FuncType(idx) = ctrl.block_type {
                    for ty in types[idx as usize].params() {
                        type_stack.push(*ty);
                    }
                }
            }
            Op::unit(OP_ELSE)
        }
        Operator::End => {
            if let Some(ctrl) = control_stack.pop() {
                type_stack.truncate(ctrl.stack_height);
                // Push result types
                match ctrl.block_type {
                    wasmparser::BlockType::Empty => {}
                    wasmparser::BlockType::Type(ty) => type_stack.push(ty),
                    wasmparser::BlockType::FuncType(idx) => {
                        for ty in types[idx as usize].results() {
                            type_stack.push(*ty);
                        }
                    }
                }
            }
            Op::unit(OP_END)
        }
        Operator::Br { relative_depth } => {
            if let Some(ctrl) = control_stack.last_mut() {
                ctrl.unreachable = true;
            }
            Op::new(OP_BR, relative_depth as u64)
        }
        Operator::BrIf { relative_depth } => {
            type_stack.pop(); // condition
            Op::new(OP_BR_IF, relative_depth as u64)
        }
        Operator::BrTable { ref targets } => {
            type_stack.pop(); // index
            if let Some(ctrl) = control_stack.last_mut() {
                ctrl.unreachable = true;
            }
            let target_list: Vec<u32> = targets.targets().collect::<Result<Vec<_>, _>>().ok()?;
            let default = targets.default();
            let idx = br_tables.len();
            br_tables.push((target_list, default));
            Op::new(OP_BR_TABLE, idx as u64)
        }
        Operator::Return => {
            if let Some(ctrl) = control_stack.last_mut() {
                ctrl.unreachable = true;
            }
            Op::unit(OP_RETURN)
        }
        Operator::Call { function_index } => {
            let type_idx = types.get(function_index as usize); // This is wrong — we need func_types
            // We can't resolve call types without func_types. Keep untyped and
            // let the interpreter handle type stack. Pop params, push results.
            // For now, just clear type tracking after calls (conservative).
            // TODO: pass func_types to properly track call types
            Op::new(OP_CALL, function_index as u64)
        }
        Operator::CallIndirect {
            type_index,
            table_index,
        } => {
            type_stack.pop(); // table index
            // Pop params, push results based on type_index
            if let Some(ft) = types.get(type_index as usize) {
                for _ in ft.params() {
                    type_stack.pop();
                }
                for ty in ft.results() {
                    type_stack.push(*ty);
                }
            }
            Op::pair(OP_CALL_INDIRECT, type_index as u32, table_index as u32)
        }
        Operator::Drop => {
            let ty = type_stack.pop().unwrap_or(ValType::I32);
            match val_byte_size(ty) {
                8 => Op::unit(OP_DROP_64),
                _ => Op::unit(OP_DROP_32),
            }
        }
        Operator::Select => {
            type_stack.pop(); // condition (i32)
            let ty = type_stack.pop().unwrap_or(ValType::I32); // val b
            type_stack.pop(); // val a
            type_stack.push(ty);
            match val_byte_size(ty) {
                8 => Op::unit(OP_SELECT_64),
                _ => Op::unit(OP_SELECT_32),
            }
        }
        Operator::TypedSelect { ty } => {
            type_stack.pop(); // condition
            type_stack.pop(); // val b
            type_stack.pop(); // val a
            type_stack.push(ty);
            match val_byte_size(ty) {
                8 => Op::unit(OP_SELECT_64),
                _ => Op::unit(OP_SELECT_32),
            }
        }

        Operator::LocalGet { local_index } => {
            let idx = local_index as usize;
            let offset = local_info.offsets[idx];
            let size = local_info.sizes[idx];
            if idx < local_info.offsets.len() {
                // Track type on type stack (look up from locals)
                // We don't have locals Vec here, but we know from size
                let ty = if size == 8 {
                    ValType::I64
                } else {
                    ValType::I32
                };
                type_stack.push(ty);
            }
            if size == 8 {
                Op::new(OP_LOCAL_GET_64, offset as u64)
            } else {
                Op::new(OP_LOCAL_GET_32, offset as u64)
            }
        }
        Operator::LocalSet { local_index } => {
            let idx = local_index as usize;
            let offset = local_info.offsets[idx];
            let size = local_info.sizes[idx];
            type_stack.pop();
            if size == 8 {
                Op::new(OP_LOCAL_SET_64, offset as u64)
            } else {
                Op::new(OP_LOCAL_SET_32, offset as u64)
            }
        }
        Operator::LocalTee { local_index } => {
            let idx = local_index as usize;
            let offset = local_info.offsets[idx];
            let size = local_info.sizes[idx];
            // tee doesn't change type stack (value stays)
            if size == 8 {
                Op::new(OP_LOCAL_TEE_64, offset as u64)
            } else {
                Op::new(OP_LOCAL_TEE_32, offset as u64)
            }
        }
        Operator::GlobalGet { global_index } => {
            // TODO: track global types on type stack
            Op::new(OP_GLOBAL_GET, global_index as u64)
        }
        Operator::GlobalSet { global_index } => {
            type_stack.pop();
            Op::new(OP_GLOBAL_SET, global_index as u64)
        }

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

/// Second pass: patch Block, If, and IfElse ops with resolved end_pc and else_pc.
///
/// Walks the ops array, maintaining a stack of block-start positions.
/// When an OP_END is encountered, it pops the stack and patches the
/// corresponding block/if op with the correct target addresses.
fn resolve_block_targets(ops: &mut [Op]) {
    // Stack entries: (start_pc, is_if)
    let mut stack: Vec<(usize, bool)> = Vec::new();
    // Records (if_pc, else_pc) for if blocks that have an else branch
    let mut else_map: Vec<(usize, usize)> = Vec::new();

    for i in 0..ops.len() {
        match ops[i].code {
            OP_BLOCK => stack.push((i, false)),
            OP_LOOP => stack.push((i, false)),
            OP_IF => stack.push((i, true)),
            OP_ELSE => {
                if let Some(&(if_pc, true)) = stack.last() {
                    else_map.push((if_pc, i));
                }
            }
            OP_END => {
                if let Some((start_pc, is_if)) = stack.pop() {
                    let start_code = ops[start_pc].code;
                    match start_code {
                        OP_BLOCK => {
                            let arity = ops[start_pc].imm_lo();
                            ops[start_pc] = Op::pair(OP_BLOCK, i as u32, arity);
                        }
                        OP_IF => {
                            let arity = ops[start_pc].imm_lo();
                            let else_pc = if is_if {
                                else_map
                                    .iter()
                                    .rev()
                                    .find(|(ip, _)| *ip == start_pc)
                                    .map(|(_, ep)| *ep)
                            } else {
                                None
                            };
                            match else_pc {
                                None => {
                                    ops[start_pc] = Op::pair(OP_IF, i as u32, arity);
                                }
                                Some(ep) => {
                                    let imm = (arity as u64) << 56 | (i as u64) << 28 | ep as u64;
                                    ops[start_pc] = Op::new(OP_IF_ELSE, imm);
                                }
                            }
                        }
                        _ => {} // OP_LOOP doesn't need patching
                    }
                }
            }
            _ => {}
        }
    }
}

/// Compile wasmparser operators directly into flat Op bytecode with resolved
/// block targets. This is the single-pass replacement for the old
/// decode_op -> Instruction -> compile_instruction pipeline.
///
/// Returns (ops, br_tables) where br_tables stores BrTable target data
/// out-of-line, indexed by the imm field of OP_BR_TABLE ops.
pub fn compile_body(
    ops_reader: wasmparser::OperatorsReader<'_>,
    types: &[FuncType],
) -> Result<(Vec<Op>, Vec<(Vec<u32>, u32)>), String> {
    let mut ops = Vec::new();
    let mut br_tables = Vec::new();

    for op_result in ops_reader {
        let op = op_result.map_err(|e| format!("op error: {e}"))?;
        if let Some(compiled) = decode_operator(&op, types, &mut br_tables) {
            ops.push(compiled);
        }
    }

    resolve_block_targets(&mut ops);
    Ok((ops, br_tables))
}
