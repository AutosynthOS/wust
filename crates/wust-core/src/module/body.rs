use wasmparser::types::TypesRef;
use wasmparser::{BlockType, FunctionBody, Operator, ValType};

use super::op::*;
use crate::task::frame::FRAME_HEADER_SIZE;

/// Number of 4-byte slots a value type occupies in the compact stack layout.
///
/// i32/f32 = 1 slot (4 bytes), i64/f64 = 2 slots (8 bytes), v128 = 4 slots (16 bytes).
pub fn slot_size(ty: ValType) -> u16 {
    match ty {
        ValType::I32 | ValType::F32 => 1,
        ValType::I64 | ValType::F64 => 2,
        ValType::V128 => 4,
        ValType::Ref(_) => 1,
    }
}

/// A pre-decoded function body: wasm bytecode → packed instruction stream.
///
/// This is the universal format shared by all engines (interpreter, JIT).
/// Each instruction is an 8-byte `InlineOp` with the opcode in byte 0
/// and a 56-bit immediate. Instructions that don't fit inline spill
/// their payload to the `data` side table via a `DataStream` reference.
#[derive(Debug, Clone, Default)]
pub struct ParsedBody {
    /// Instruction stream: one `InlineOp` per wasm instruction.
    pub ops: Vec<InlineOp>,
    /// Side table for oversized immediates (constants, etc).
    pub data: Vec<u8>,
    /// Block metadata, indexed by block index.
    pub blocks: Vec<Block>,
    /// Operand stack depth (in 4-byte slots) before each instruction.
    ///
    /// `operand_depth[pc]` is the slot offset of the operand stack top
    /// relative to the operand base (which starts after locals). This
    /// enables resume at an arbitrary PC without runtime stack tracking,
    /// and determines callee frame placement on Call.
    pub operand_depth: Vec<u16>,
}

/// Metadata for a structured control flow region (block/loop/if/function).
#[derive(Debug, Clone)]
pub struct Block {
    pub kind: BlockKind,
    /// PC of the block opener (block/loop/if instruction).
    pub start_pc: u32,
    /// PC of the `end` instruction (patched when `end` is parsed).
    pub end_pc: u32,
    /// PC of the `else` instruction (only for `If`, 0 if no else).
    pub else_pc: u32,
    /// Number of result values this block produces.
    pub result_count: u32,
    /// Number of parameter values this block consumes.
    pub param_count: u32,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BlockKind {
    /// Implicit function-level block.
    Function,
    Block,
    Loop,
    If,
}

impl ParsedBody {
    /// Decode a wasm function body into a pre-decoded instruction stream.
    ///
    /// Computes operand depth in the same pass using the type stack.
    /// `local_types` = params ++ declared locals. `result_types` = function results.
    pub fn parse(
        reader: &FunctionBody,
        types: &TypesRef,
        local_types: &[ValType],
        result_types: &[ValType],
        local_byte_offsets: &[u16],
    ) -> Result<Self, anyhow::Error> {
        let mut d = BodyDecoder::new(types, local_types, result_types, local_byte_offsets);
        d.decode(reader)?;
        Ok(d.body)
    }

    /// Body for an imported function (no wasm bytecode to decode).
    pub fn import() -> Self {
        ParsedBody {
            ops: vec![pack(OpCode::Unreachable)],
            data: Vec::new(),
            blocks: Vec::new(),
            operand_depth: vec![0],
        }
    }
}

// ---------------------------------------------------------------------------
// Block tracking for structured control flow
// ---------------------------------------------------------------------------

/// Saved state at block entry for depth restoration.
#[derive(Clone)]
struct BlockEntry {
    /// Index into ParsedBody::blocks.
    block_idx: u32,
    /// type_stack height at block entry (after consuming params).
    type_stack_height: usize,
    /// Result types for this block.
    result_types: Vec<ValType>,
    /// Param types for this block.
    param_types: Vec<ValType>,
}

// ---------------------------------------------------------------------------
// Decoder
// ---------------------------------------------------------------------------

struct BodyDecoder<'a> {
    body: ParsedBody,
    /// Control flow block stack (for structured branch targets).
    block_stack: Vec<BlockEntry>,
    types: &'a TypesRef<'a>,
    /// Local variable types (params + declared locals).
    local_types: &'a [ValType],
    /// Function result types.
    result_types: &'a [ValType],
    /// Byte offset of each local from the locals base (fp + FRAME_HEADER_SIZE).
    local_byte_offsets: &'a [u16],
    /// Type of each value on the operand stack.
    type_stack: Vec<ValType>,
    /// True after an unconditional branch (Br, Return, Unreachable).
    /// In dead code, we don't track the type stack.
    unreachable: bool,
}

impl<'a> BodyDecoder<'a> {
    fn new(
        types: &'a TypesRef<'a>,
        local_types: &'a [ValType],
        result_types: &'a [ValType],
        local_byte_offsets: &'a [u16],
    ) -> Self {
        Self {
            body: ParsedBody::default(),
            block_stack: Vec::new(),
            types,
            local_types,
            result_types,
            local_byte_offsets,
            type_stack: Vec::new(),
            unreachable: false,
        }
    }

    /// Compute operand depth from the type stack.
    fn depth(&self) -> u16 {
        self.type_stack.iter().map(|t| slot_size(*t)).sum()
    }

    /// Record current depth.
    fn record_depth(&mut self) {
        self.body.operand_depth.push(self.depth());
    }

    /// Record current depth and emit an instruction.
    fn emit_op(&mut self, op: InlineOp) {
        self.record_depth();
        self.body.ops.push(op);
    }

    fn push(&mut self, ty: ValType) {
        self.type_stack.push(ty);
    }

    fn pop(&mut self) -> ValType {
        self.type_stack.pop().expect("type stack underflow")
    }

    fn decode(&mut self, reader: &FunctionBody) -> Result<(), anyhow::Error> {
        // Implicit function-level block (index 0).
        let func_block = self.open_block(
            BlockKind::Function,
            self.result_types.to_vec(),
            vec![],
        );
        self.block_stack.push(func_block);

        for op in reader.get_operators_reader()? {
            self.decode_op(op?)?;
        }
        Ok(())
    }

    fn open_block(
        &mut self,
        kind: BlockKind,
        result_types: Vec<ValType>,
        param_types: Vec<ValType>,
    ) -> BlockEntry {
        let idx = self.body.blocks.len() as u32;
        self.body.blocks.push(Block {
            kind,
            start_pc: self.body.ops.len() as u32,
            end_pc: 0,
            else_pc: 0,
            result_count: result_types.len() as u32,
            param_count: param_types.len() as u32,
        });
        BlockEntry {
            block_idx: idx,
            type_stack_height: self.type_stack.len() - param_types.len(),
            result_types,
            param_types,
        }
    }

    fn resolve_block_type(&self, bt: BlockType) -> (Vec<ValType>, Vec<ValType>) {
        match bt {
            BlockType::Empty => (vec![], vec![]),
            BlockType::Type(ty) => (vec![ty], vec![]),
            BlockType::FuncType(idx) => {
                let core_type_id = self.types.core_type_at_in_module(idx);
                let func_type = self.types[core_type_id].unwrap_func();
                (
                    func_type.results().to_vec(),
                    func_type.params().to_vec(),
                )
            }
        }
    }

    fn resolve_branch_target(&self, relative_depth: u32) -> u32 {
        let entry = &self.block_stack[self.block_stack.len() - 1 - relative_depth as usize];
        entry.block_idx
    }

    fn decode_op(&mut self, op: Operator) -> Result<(), anyhow::Error> {
        // In dead code (after unconditional branch), only track block
        // structure — don't simulate the type stack.
        if self.unreachable {
            match op {
                Operator::Block { blockty } => {
                    let (rt, pt) = self.resolve_block_type(blockty);
                    let entry = self.open_block(BlockKind::Block, rt, pt);
                    let idx = entry.block_idx;
                    self.block_stack.push(entry);
                    self.emit_op(pack_imm_u(OpCode::Block, idx));
                }
                Operator::Loop { blockty } => {
                    let (rt, pt) = self.resolve_block_type(blockty);
                    let entry = self.open_block(BlockKind::Loop, rt, pt);
                    let idx = entry.block_idx;
                    self.block_stack.push(entry);
                    self.emit_op(pack_imm_u(OpCode::Loop, idx));
                }
                Operator::If { blockty } => {
                    let (rt, pt) = self.resolve_block_type(blockty);
                    let entry = self.open_block(BlockKind::If, rt, pt);
                    let idx = entry.block_idx;
                    self.block_stack.push(entry);
                    self.emit_op(pack_imm_u(OpCode::If, idx));
                }
                Operator::Else => {
                    let entry = self.block_stack.last().expect("else without block");
                    let idx = entry.block_idx;
                    self.body.blocks[idx as usize].else_pc = self.body.ops.len() as u32;
                    // Restore type stack to block entry + params.
                    self.type_stack.truncate(entry.type_stack_height);
                    self.type_stack.extend_from_slice(&entry.param_types);
                    self.unreachable = false;
                    self.emit_op(pack_imm_u(OpCode::Else, idx));
                }
                Operator::End => {
                    let entry = self.block_stack.pop().expect("end without block");
                    self.body.blocks[entry.block_idx as usize].end_pc =
                        self.body.ops.len() as u32;
                    // Restore type stack to block base + results.
                    self.type_stack.truncate(entry.type_stack_height);
                    self.type_stack.extend_from_slice(&entry.result_types);
                    self.unreachable = false;
                    self.emit_op(pack_imm_u(OpCode::End, entry.block_idx));
                }
                _ => {
                    // Emit a placeholder depth for dead code.
                    self.emit_op(pack(OpCode::Nop));
                }
            }
            return Ok(());
        }

        match op {
            // --- Control flow ---
            Operator::Nop => {
                self.emit_op(pack(OpCode::Nop));
            }
            Operator::Unreachable => {
                self.emit_op(pack(OpCode::Unreachable));
                self.unreachable = true;
            }
            Operator::Return => {
                self.emit_op(pack(OpCode::Return));
                self.unreachable = true;
            }

            Operator::Block { blockty } => {
                let (rt, pt) = self.resolve_block_type(blockty);
                let entry = self.open_block(BlockKind::Block, rt, pt);
                let idx = entry.block_idx;
                self.block_stack.push(entry);
                self.emit_op(pack_imm_u(OpCode::Block, idx));
            }
            Operator::Loop { blockty } => {
                let (rt, pt) = self.resolve_block_type(blockty);
                let entry = self.open_block(BlockKind::Loop, rt, pt);
                let idx = entry.block_idx;
                self.block_stack.push(entry);
                self.emit_op(pack_imm_u(OpCode::Loop, idx));
            }
            Operator::If { blockty } => {
                self.record_depth();
                let cond = self.pop();
                debug_assert_eq!(cond, ValType::I32);
                let (rt, pt) = self.resolve_block_type(blockty);
                let entry = self.open_block(BlockKind::If, rt, pt);
                let idx = entry.block_idx;
                self.block_stack.push(entry);
                self.body.ops.push(pack_imm_u(OpCode::If, idx));
            }
            Operator::Else => {
                let entry = self.block_stack.last().expect("else without block");
                let idx = entry.block_idx;
                let height = entry.type_stack_height;
                let params = entry.param_types.clone();
                self.body.blocks[idx as usize].else_pc = self.body.ops.len() as u32;
                self.emit_op(pack_imm_u(OpCode::Else, idx));
                self.type_stack.truncate(height);
                self.type_stack.extend_from_slice(&params);
            }
            Operator::End => {
                let entry = self.block_stack.pop().expect("end without block");
                self.body.blocks[entry.block_idx as usize].end_pc =
                    self.body.ops.len() as u32;
                self.emit_op(pack_imm_u(OpCode::End, entry.block_idx));
                self.type_stack.truncate(entry.type_stack_height);
                self.type_stack.extend_from_slice(&entry.result_types);
            }

            Operator::Br { relative_depth } => {
                let target = self.resolve_branch_target(relative_depth);
                self.emit_op(pack_imm_u(OpCode::Br, target));
                self.unreachable = true;
            }
            Operator::BrIf { relative_depth } => {
                let target = self.resolve_branch_target(relative_depth);
                self.emit_op(pack_imm_u(OpCode::BrIf, target));
                let cond = self.pop();
                debug_assert_eq!(cond, ValType::I32);
            }

            Operator::Call { function_index } => {
                let core_type_id = self.types.core_function_at(function_index);
                let func_type = self.types[core_type_id].unwrap_func();
                self.emit_u(OpCode::Call, function_index);
                for _ in func_type.params() {
                    self.pop();
                }
                for ty in func_type.results() {
                    self.push(*ty);
                }
            }

            // --- Constants ---
            Operator::I32Const { value } => {
                self.emit_signed(OpCode::I32Const, value as i64, &value.to_le_bytes());
                self.push(ValType::I32);
            }
            Operator::I64Const { value } => {
                self.emit_signed(OpCode::I64Const, value, &value.to_le_bytes());
                self.push(ValType::I64);
            }
            Operator::F32Const { value } => {
                self.emit_data(OpCode::F32Const, &value.bits().to_le_bytes());
                self.push(ValType::F32);
            }
            Operator::F64Const { value } => {
                self.emit_data(OpCode::F64Const, &value.bits().to_le_bytes());
                self.push(ValType::F64);
            }

            // --- Locals ---
            Operator::LocalGet { local_index } => {
                let ty = self.local_types[local_index as usize];
                let fp_offset = FRAME_HEADER_SIZE as u32
                    + self.local_byte_offsets[local_index as usize] as u32;
                let opcode = match slot_size(ty) {
                    1 => OpCode::LocalGetI32,
                    2 => OpCode::LocalGetI64,
                    _ => todo!("LocalGet for {ty:?}"),
                };
                self.emit_op(pack_imm_u(opcode, fp_offset));
                self.push(ty);
            }
            Operator::LocalSet { local_index } => {
                let ty = self.local_types[local_index as usize];
                let fp_offset = FRAME_HEADER_SIZE as u32
                    + self.local_byte_offsets[local_index as usize] as u32;
                let opcode = match slot_size(ty) {
                    1 => OpCode::LocalSetI32,
                    2 => OpCode::LocalSetI64,
                    _ => todo!("LocalSet for {ty:?}"),
                };
                self.emit_op(pack_imm_u(opcode, fp_offset));
                self.pop();
            }
            Operator::LocalTee { local_index } => {
                let ty = self.local_types[local_index as usize];
                let fp_offset = FRAME_HEADER_SIZE as u32
                    + self.local_byte_offsets[local_index as usize] as u32;
                let opcode = match slot_size(ty) {
                    1 => OpCode::LocalTeeI32,
                    2 => OpCode::LocalTeeI64,
                    _ => todo!("LocalTee for {ty:?}"),
                };
                self.emit_op(pack_imm_u(opcode, fp_offset));
            }

            // --- Globals ---
            Operator::GlobalGet { global_index } => {
                // TODO: look up global type properly.
                self.emit_u(OpCode::GlobalGet, global_index);
                self.push(ValType::I32);
            }
            Operator::GlobalSet { global_index } => {
                self.emit_u(OpCode::GlobalSet, global_index);
                self.pop();
            }

            // --- Stack manipulation ---
            Operator::Drop => {
                let ty = *self.type_stack.last().unwrap();
                let slots = slot_size(ty);
                self.emit_op(pack_imm_u(OpCode::Drop, slots as u32));
                self.pop();
            }
            Operator::Select | Operator::TypedSelect { .. } => {
                // Stack before: [val val i32_cond], depth includes all three.
                let slots = slot_size(self.type_stack[self.type_stack.len() - 2]);
                self.emit_op(pack_imm_u(OpCode::Select, slots as u32));
                self.pop(); // cond
                self.pop(); // b
                // a stays
            }

            // --- References ---
            Operator::RefNull { .. } => {
                self.emit_op(pack(OpCode::RefNull));
                self.push(ValType::I32); // TODO: proper ref type
            }

            // --- i32 binary (pop 2 i32, push 1 i32) ---
            Operator::I32Add => self.emit_binary(OpCode::I32Add, ValType::I32),
            Operator::I32Sub => self.emit_binary(OpCode::I32Sub, ValType::I32),
            Operator::I32Mul => self.emit_binary(OpCode::I32Mul, ValType::I32),
            Operator::I32DivS => self.emit_binary(OpCode::I32DivS, ValType::I32),
            Operator::I32DivU => self.emit_binary(OpCode::I32DivU, ValType::I32),
            Operator::I32RemS => self.emit_binary(OpCode::I32RemS, ValType::I32),
            Operator::I32RemU => self.emit_binary(OpCode::I32RemU, ValType::I32),
            Operator::I32And => self.emit_binary(OpCode::I32And, ValType::I32),
            Operator::I32Or => self.emit_binary(OpCode::I32Or, ValType::I32),
            Operator::I32Xor => self.emit_binary(OpCode::I32Xor, ValType::I32),
            Operator::I32Shl => self.emit_binary(OpCode::I32Shl, ValType::I32),
            Operator::I32ShrS => self.emit_binary(OpCode::I32ShrS, ValType::I32),
            Operator::I32ShrU => self.emit_binary(OpCode::I32ShrU, ValType::I32),
            Operator::I32Rotl => self.emit_binary(OpCode::I32Rotl, ValType::I32),
            Operator::I32Rotr => self.emit_binary(OpCode::I32Rotr, ValType::I32),

            // --- i32 comparison (pop 2 i32, push 1 i32) ---
            Operator::I32Eq => self.emit_binary(OpCode::I32Eq, ValType::I32),
            Operator::I32Ne => self.emit_binary(OpCode::I32Ne, ValType::I32),
            Operator::I32LtS => self.emit_binary(OpCode::I32LtS, ValType::I32),
            Operator::I32LtU => self.emit_binary(OpCode::I32LtU, ValType::I32),
            Operator::I32GtS => self.emit_binary(OpCode::I32GtS, ValType::I32),
            Operator::I32GtU => self.emit_binary(OpCode::I32GtU, ValType::I32),
            Operator::I32LeS => self.emit_binary(OpCode::I32LeS, ValType::I32),
            Operator::I32LeU => self.emit_binary(OpCode::I32LeU, ValType::I32),
            Operator::I32GeS => self.emit_binary(OpCode::I32GeS, ValType::I32),
            Operator::I32GeU => self.emit_binary(OpCode::I32GeU, ValType::I32),

            // --- i32 test (pop 1 i32, push 1 i32) ---
            Operator::I32Eqz => self.emit_unary(OpCode::I32Eqz, ValType::I32),

            // --- i32 unary (pop 1 i32, push 1 i32) ---
            Operator::I32Clz => self.emit_unary(OpCode::I32Clz, ValType::I32),
            Operator::I32Ctz => self.emit_unary(OpCode::I32Ctz, ValType::I32),
            Operator::I32Popcnt => self.emit_unary(OpCode::I32Popcnt, ValType::I32),
            Operator::I32Extend8S => self.emit_unary(OpCode::I32Extend8S, ValType::I32),
            Operator::I32Extend16S => self.emit_unary(OpCode::I32Extend16S, ValType::I32),

            // --- i32 conversion (pop other, push i32) ---
            Operator::I32WrapI64 => self.emit_convert(OpCode::I32WrapI64, ValType::I32),
            Operator::I32TruncF32S => self.emit_convert(OpCode::I32TruncF32S, ValType::I32),
            Operator::I32TruncF32U => self.emit_convert(OpCode::I32TruncF32U, ValType::I32),
            Operator::I32TruncF64S => self.emit_convert(OpCode::I32TruncF64S, ValType::I32),
            Operator::I32TruncF64U => self.emit_convert(OpCode::I32TruncF64U, ValType::I32),
            Operator::I32TruncSatF32S => self.emit_convert(OpCode::I32TruncSatF32S, ValType::I32),
            Operator::I32TruncSatF32U => self.emit_convert(OpCode::I32TruncSatF32U, ValType::I32),
            Operator::I32TruncSatF64S => self.emit_convert(OpCode::I32TruncSatF64S, ValType::I32),
            Operator::I32TruncSatF64U => self.emit_convert(OpCode::I32TruncSatF64U, ValType::I32),
            Operator::I32ReinterpretF32 => self.emit_convert(OpCode::I32ReinterpretF32, ValType::I32),

            // --- i64 binary (pop 2 i64, push 1 i64) ---
            Operator::I64Add => self.emit_binary(OpCode::I64Add, ValType::I64),
            Operator::I64Sub => self.emit_binary(OpCode::I64Sub, ValType::I64),
            Operator::I64Mul => self.emit_binary(OpCode::I64Mul, ValType::I64),
            Operator::I64DivS => self.emit_binary(OpCode::I64DivS, ValType::I64),
            Operator::I64DivU => self.emit_binary(OpCode::I64DivU, ValType::I64),
            Operator::I64RemS => self.emit_binary(OpCode::I64RemS, ValType::I64),
            Operator::I64RemU => self.emit_binary(OpCode::I64RemU, ValType::I64),
            Operator::I64And => self.emit_binary(OpCode::I64And, ValType::I64),
            Operator::I64Or => self.emit_binary(OpCode::I64Or, ValType::I64),
            Operator::I64Xor => self.emit_binary(OpCode::I64Xor, ValType::I64),
            Operator::I64Shl => self.emit_binary(OpCode::I64Shl, ValType::I64),
            Operator::I64ShrS => self.emit_binary(OpCode::I64ShrS, ValType::I64),
            Operator::I64ShrU => self.emit_binary(OpCode::I64ShrU, ValType::I64),
            Operator::I64Rotl => self.emit_binary(OpCode::I64Rotl, ValType::I64),
            Operator::I64Rotr => self.emit_binary(OpCode::I64Rotr, ValType::I64),

            // --- i64 comparison (pop 2 i64, push 1 i32) ---
            Operator::I64Eq => self.emit_cmp(OpCode::I64Eq),
            Operator::I64Ne => self.emit_cmp(OpCode::I64Ne),
            Operator::I64LtS => self.emit_cmp(OpCode::I64LtS),
            Operator::I64LtU => self.emit_cmp(OpCode::I64LtU),
            Operator::I64GtS => self.emit_cmp(OpCode::I64GtS),
            Operator::I64GtU => self.emit_cmp(OpCode::I64GtU),
            Operator::I64LeS => self.emit_cmp(OpCode::I64LeS),
            Operator::I64LeU => self.emit_cmp(OpCode::I64LeU),
            Operator::I64GeS => self.emit_cmp(OpCode::I64GeS),
            Operator::I64GeU => self.emit_cmp(OpCode::I64GeU),

            // --- i64 test (pop 1 i64, push 1 i32) ---
            Operator::I64Eqz => self.emit_test(OpCode::I64Eqz),

            // --- i64 unary (pop 1 i64, push 1 i64) ---
            Operator::I64Clz => self.emit_unary(OpCode::I64Clz, ValType::I64),
            Operator::I64Ctz => self.emit_unary(OpCode::I64Ctz, ValType::I64),
            Operator::I64Popcnt => self.emit_unary(OpCode::I64Popcnt, ValType::I64),
            Operator::I64Extend8S => self.emit_unary(OpCode::I64Extend8S, ValType::I64),
            Operator::I64Extend16S => self.emit_unary(OpCode::I64Extend16S, ValType::I64),
            Operator::I64Extend32S => self.emit_unary(OpCode::I64Extend32S, ValType::I64),

            // --- i64 conversion (pop other, push i64) ---
            Operator::I64ExtendI32S => self.emit_convert(OpCode::I64ExtendI32S, ValType::I64),
            Operator::I64ExtendI32U => self.emit_convert(OpCode::I64ExtendI32U, ValType::I64),
            Operator::I64TruncF32S => self.emit_convert(OpCode::I64TruncF32S, ValType::I64),
            Operator::I64TruncF32U => self.emit_convert(OpCode::I64TruncF32U, ValType::I64),
            Operator::I64TruncF64S => self.emit_convert(OpCode::I64TruncF64S, ValType::I64),
            Operator::I64TruncF64U => self.emit_convert(OpCode::I64TruncF64U, ValType::I64),
            Operator::I64TruncSatF32S => self.emit_convert(OpCode::I64TruncSatF32S, ValType::I64),
            Operator::I64TruncSatF32U => self.emit_convert(OpCode::I64TruncSatF32U, ValType::I64),
            Operator::I64TruncSatF64S => self.emit_convert(OpCode::I64TruncSatF64S, ValType::I64),
            Operator::I64TruncSatF64U => self.emit_convert(OpCode::I64TruncSatF64U, ValType::I64),
            Operator::I64ReinterpretF64 => self.emit_convert(OpCode::I64ReinterpretF64, ValType::I64),

            // --- f32 binary (pop 2 f32, push 1 f32) ---
            Operator::F32Add => self.emit_binary(OpCode::F32Add, ValType::F32),
            Operator::F32Sub => self.emit_binary(OpCode::F32Sub, ValType::F32),
            Operator::F32Mul => self.emit_binary(OpCode::F32Mul, ValType::F32),
            Operator::F32Div => self.emit_binary(OpCode::F32Div, ValType::F32),
            Operator::F32Min => self.emit_binary(OpCode::F32Min, ValType::F32),
            Operator::F32Max => self.emit_binary(OpCode::F32Max, ValType::F32),
            Operator::F32Copysign => self.emit_binary(OpCode::F32Copysign, ValType::F32),

            // --- f32 unary (pop 1 f32, push 1 f32) ---
            Operator::F32Abs => self.emit_unary(OpCode::F32Abs, ValType::F32),
            Operator::F32Neg => self.emit_unary(OpCode::F32Neg, ValType::F32),
            Operator::F32Sqrt => self.emit_unary(OpCode::F32Sqrt, ValType::F32),
            Operator::F32Ceil => self.emit_unary(OpCode::F32Ceil, ValType::F32),
            Operator::F32Floor => self.emit_unary(OpCode::F32Floor, ValType::F32),
            Operator::F32Trunc => self.emit_unary(OpCode::F32Trunc, ValType::F32),
            Operator::F32Nearest => self.emit_unary(OpCode::F32Nearest, ValType::F32),

            // --- f32 comparison (pop 2 f32, push 1 i32) ---
            Operator::F32Eq => self.emit_cmp(OpCode::F32Eq),
            Operator::F32Ne => self.emit_cmp(OpCode::F32Ne),
            Operator::F32Lt => self.emit_cmp(OpCode::F32Lt),
            Operator::F32Gt => self.emit_cmp(OpCode::F32Gt),
            Operator::F32Le => self.emit_cmp(OpCode::F32Le),
            Operator::F32Ge => self.emit_cmp(OpCode::F32Ge),

            // --- f32 conversion (pop other, push f32) ---
            Operator::F32ConvertI32S => self.emit_convert(OpCode::F32ConvertI32S, ValType::F32),
            Operator::F32ConvertI32U => self.emit_convert(OpCode::F32ConvertI32U, ValType::F32),
            Operator::F32ConvertI64S => self.emit_convert(OpCode::F32ConvertI64S, ValType::F32),
            Operator::F32ConvertI64U => self.emit_convert(OpCode::F32ConvertI64U, ValType::F32),
            Operator::F32DemoteF64 => self.emit_convert(OpCode::F32DemoteF64, ValType::F32),
            Operator::F32ReinterpretI32 => self.emit_convert(OpCode::F32ReinterpretI32, ValType::F32),

            // --- f64 binary (pop 2 f64, push 1 f64) ---
            Operator::F64Add => self.emit_binary(OpCode::F64Add, ValType::F64),
            Operator::F64Sub => self.emit_binary(OpCode::F64Sub, ValType::F64),
            Operator::F64Mul => self.emit_binary(OpCode::F64Mul, ValType::F64),
            Operator::F64Div => self.emit_binary(OpCode::F64Div, ValType::F64),
            Operator::F64Min => self.emit_binary(OpCode::F64Min, ValType::F64),
            Operator::F64Max => self.emit_binary(OpCode::F64Max, ValType::F64),
            Operator::F64Copysign => self.emit_binary(OpCode::F64Copysign, ValType::F64),

            // --- f64 unary (pop 1 f64, push 1 f64) ---
            Operator::F64Abs => self.emit_unary(OpCode::F64Abs, ValType::F64),
            Operator::F64Neg => self.emit_unary(OpCode::F64Neg, ValType::F64),
            Operator::F64Sqrt => self.emit_unary(OpCode::F64Sqrt, ValType::F64),
            Operator::F64Ceil => self.emit_unary(OpCode::F64Ceil, ValType::F64),
            Operator::F64Floor => self.emit_unary(OpCode::F64Floor, ValType::F64),
            Operator::F64Trunc => self.emit_unary(OpCode::F64Trunc, ValType::F64),
            Operator::F64Nearest => self.emit_unary(OpCode::F64Nearest, ValType::F64),

            // --- f64 comparison (pop 2 f64, push 1 i32) ---
            Operator::F64Eq => self.emit_cmp(OpCode::F64Eq),
            Operator::F64Ne => self.emit_cmp(OpCode::F64Ne),
            Operator::F64Lt => self.emit_cmp(OpCode::F64Lt),
            Operator::F64Gt => self.emit_cmp(OpCode::F64Gt),
            Operator::F64Le => self.emit_cmp(OpCode::F64Le),
            Operator::F64Ge => self.emit_cmp(OpCode::F64Ge),

            // --- f64 conversion (pop other, push f64) ---
            Operator::F64ConvertI32S => self.emit_convert(OpCode::F64ConvertI32S, ValType::F64),
            Operator::F64ConvertI32U => self.emit_convert(OpCode::F64ConvertI32U, ValType::F64),
            Operator::F64ConvertI64S => self.emit_convert(OpCode::F64ConvertI64S, ValType::F64),
            Operator::F64ConvertI64U => self.emit_convert(OpCode::F64ConvertI64U, ValType::F64),
            Operator::F64PromoteF32 => self.emit_convert(OpCode::F64PromoteF32, ValType::F64),
            Operator::F64ReinterpretI64 => self.emit_convert(OpCode::F64ReinterpretI64, ValType::F64),

            // Unsupported opcodes trap cleanly.
            _ => {
                self.emit_op(pack(OpCode::Unreachable));
            }
        }
        Ok(())
    }

    // --- Emit helpers ---

    /// Binary op: pop 2 of the same type, push 1 of result_type.
    fn emit_binary(&mut self, opcode: OpCode, result_type: ValType) {
        self.emit_op(pack(opcode));
        self.pop();
        self.pop();
        self.push(result_type);
    }

    /// Unary op: pop 1, push 1 of the same type.
    fn emit_unary(&mut self, opcode: OpCode, result_type: ValType) {
        self.emit_op(pack(opcode));
        self.pop();
        self.push(result_type);
    }

    /// Comparison: pop 2 of any type, push i32.
    fn emit_cmp(&mut self, opcode: OpCode) {
        self.emit_op(pack(opcode));
        self.pop();
        self.pop();
        self.push(ValType::I32);
    }

    /// Test: pop 1 of any type, push i32.
    fn emit_test(&mut self, opcode: OpCode) {
        self.emit_op(pack(opcode));
        self.pop();
        self.push(ValType::I32);
    }

    /// Conversion: pop 1 of source type, push 1 of dest type.
    fn emit_convert(&mut self, opcode: OpCode, dest_type: ValType) {
        self.emit_op(pack(opcode));
        self.pop();
        self.push(dest_type);
    }

    /// Emit an unsigned immediate, inlining if it fits in 24 bits.
    fn emit_u(&mut self, opcode: OpCode, value: u32) {
        if fits_imm24_unsigned(value as u64) {
            self.emit_op(pack_imm_u(opcode, value));
        } else {
            self.emit_data(opcode, &value.to_le_bytes());
        }
    }

    /// Emit a signed immediate, inlining if it fits in 24 bits.
    fn emit_signed(&mut self, opcode: OpCode, value: i64, full_bytes: &[u8]) {
        if fits_imm24(value) {
            self.emit_op(pack_imm(opcode, value as i32));
        } else {
            self.emit_data(opcode, full_bytes);
        }
    }

    /// Spill to the data side table via a `DataStream` reference.
    fn emit_data(&mut self, opcode: OpCode, bytes: &[u8]) {
        let offset = self.body.data.len() as u32;
        debug_assert!(fits_imm24_unsigned(offset as u64), "data offset overflow");
        self.emit_op(pack_imm_u(OpCode::DataStream, offset));
        self.body.data.push(opcode as u8);
        self.body.data.extend_from_slice(bytes);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ParsedModule;

    /// Parse a WAT module and return the operand_depth table for the
    /// first exported function.
    fn depth_table(wat: &str) -> (Vec<u16>, Vec<OpCode>) {
        let wasm = wat::parse_str(wat).expect("bad WAT");
        let module = ParsedModule::new(&wasm).expect("parse failed");
        let func_idx = module.exports.values().next().expect("no export");
        let meta = &module.funcs[**func_idx as usize];
        let opcodes: Vec<OpCode> = meta.body.ops.iter().map(|op| {
            if op.opcode() == OpCode::DataStream {
                let offset = op.immediate_u32() as usize;
                unsafe { std::mem::transmute::<u8, OpCode>(meta.body.data[offset]) }
            } else {
                op.opcode()
            }
        }).collect();
        (meta.body.operand_depth.clone(), opcodes)
    }

    #[test]
    fn depth_i32_add_two_consts() {
        let (depths, ops) = depth_table(r#"
            (module (func (export "f") (result i32)
                i32.const 1
                i32.const 2
                i32.add
            ))
        "#);
        assert_eq!(ops[0], OpCode::I32Const);
        assert_eq!(depths[0], 0);
        assert_eq!(depths[1], 1);
        assert_eq!(depths[2], 2);
        assert_eq!(depths[3], 1); // End
    }

    #[test]
    fn depth_i64_consts() {
        let (depths, _) = depth_table(r#"
            (module (func (export "f") (result i64)
                i64.const 1
                i64.const 2
                i64.add
            ))
        "#);
        assert_eq!(depths[0], 0);
        assert_eq!(depths[1], 2);
        assert_eq!(depths[2], 4);
        assert_eq!(depths[3], 2); // End
    }

    #[test]
    fn depth_local_get_i32() {
        let (depths, _) = depth_table(r#"
            (module (func (export "f") (param i32) (result i32)
                local.get 0
            ))
        "#);
        assert_eq!(depths[0], 0);
        assert_eq!(depths[1], 1); // End
    }

    #[test]
    fn depth_mixed_types() {
        let (depths, _) = depth_table(r#"
            (module (func (export "f")
                i32.const 1
                i64.const 2
                drop
                drop
            ))
        "#);
        assert_eq!(depths[0], 0);
        assert_eq!(depths[1], 1);
        assert_eq!(depths[2], 3);
        assert_eq!(depths[3], 1);
        assert_eq!(depths[4], 0); // End
    }

    #[test]
    fn depth_if_else() {
        let (depths, ops) = depth_table(r#"
            (module (func (export "f") (param i32) (result i32)
                local.get 0
                if (result i32)
                    i32.const 1
                else
                    i32.const 2
                end
            ))
        "#);
        assert_eq!(ops[0], OpCode::LocalGetI32);
        assert_eq!(depths[0], 0);
        assert_eq!(ops[1], OpCode::If);
        assert_eq!(depths[1], 1);
        assert_eq!(ops[2], OpCode::I32Const);
        assert_eq!(depths[2], 0);
        assert_eq!(ops[3], OpCode::Else);
        assert_eq!(depths[3], 1);
        assert_eq!(ops[4], OpCode::I32Const);
        assert_eq!(depths[4], 0);
        assert_eq!(ops[5], OpCode::End);
        assert_eq!(depths[5], 1);
        assert_eq!(ops[6], OpCode::End); // function End
        assert_eq!(depths[6], 1);
    }

    #[test]
    fn depth_call() {
        let (depths, _) = depth_table(r#"
            (module
                (func $add (param i32 i32) (result i32) local.get 0 local.get 1 i32.add)
                (func (export "f") (result i32)
                    i32.const 3
                    i32.const 4
                    call $add
                ))
        "#);
        assert_eq!(depths[0], 0);
        assert_eq!(depths[1], 1);
        assert_eq!(depths[2], 2);
        assert_eq!(depths[3], 1); // End
    }

    #[test]
    fn drop_encodes_slot_size() {
        let wasm = wat::parse_str(r#"
            (module (func (export "f")
                i64.const 42
                drop
            ))
        "#).unwrap();
        let module = ParsedModule::new(&wasm).unwrap();
        let func_idx = module.exports.values().next().unwrap();
        let meta = &module.funcs[**func_idx as usize];
        // The drop instruction should encode slot_size=2 (i64) in its immediate.
        let drop_op = meta.body.ops[1]; // [I64Const, Drop, End]
        assert_eq!(drop_op.opcode(), OpCode::Drop);
        assert_eq!(drop_op.immediate_u32(), 2); // i64 = 2 slots
    }
}
