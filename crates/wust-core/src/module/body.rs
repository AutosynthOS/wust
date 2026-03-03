use wasmparser::types::TypesRef;
use wasmparser::{BlockType, FunctionBody, Operator};

use super::op::*;

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
    pub fn parse(reader: &FunctionBody, types: &TypesRef) -> Result<Self, anyhow::Error> {
        let mut decoder = BodyDecoder::new(types);
        decoder.decode(reader)?;
        Ok(decoder.body)
    }

    /// Body for an imported function (no wasm bytecode to decode).
    pub fn import() -> Self {
        ParsedBody {
            ops: vec![pack(OpCode::Unreachable)],
            data: Vec::new(),
            blocks: Vec::new(),
        }
    }
}

/// Internal decoder state, separated from `ParsedBody` to keep the
/// public API clean.
struct BodyDecoder<'a> {
    body: ParsedBody,
    block_stack: Vec<u32>,
    types: &'a TypesRef<'a>,
}

impl<'a> BodyDecoder<'a> {
    fn new(types: &'a TypesRef<'a>) -> Self {
        Self {
            body: ParsedBody::default(),
            block_stack: Vec::new(),
            types,
        }
    }

    fn decode(&mut self, reader: &FunctionBody) -> Result<(), anyhow::Error> {
        // Implicit function-level block (index 0).
        // Result count is patched later by the module builder.
        let func_block = self.open_block(BlockKind::Function, 0, 0);
        self.block_stack.push(func_block);

        for op in reader.get_operators_reader()? {
            self.decode_op(op?)?;
        }
        Ok(())
    }

    fn open_block(&mut self, kind: BlockKind, result_count: u32, param_count: u32) -> u32 {
        let idx = self.body.blocks.len() as u32;
        self.body.blocks.push(Block {
            kind,
            start_pc: self.body.ops.len() as u32,
            end_pc: 0,
            else_pc: 0,
            result_count,
            param_count,
        });
        idx
    }

    fn resolve_block_type(&self, bt: BlockType) -> (u32, u32) {
        match bt {
            BlockType::Empty => (0, 0),
            BlockType::Type(_) => (1, 0),
            BlockType::FuncType(idx) => {
                let core_type_id = self.types.core_type_at_in_module(idx);
                let func_type = self.types[core_type_id].unwrap_func();
                (
                    func_type.results().len() as u32,
                    func_type.params().len() as u32,
                )
            }
        }
    }

    fn resolve_branch_target(&self, relative_depth: u32) -> u32 {
        self.block_stack[self.block_stack.len() - 1 - relative_depth as usize]
    }

    fn decode_op(&mut self, op: Operator) -> Result<(), anyhow::Error> {
        match op {
            // --- Control flow ---
            Operator::Nop => self.emit(OpCode::Nop),
            Operator::Unreachable => self.emit(OpCode::Unreachable),
            Operator::Return => self.emit(OpCode::Return),

            Operator::Block { blockty } => {
                let (rc, pc) = self.resolve_block_type(blockty);
                let idx = self.open_block(BlockKind::Block, rc, pc);
                self.block_stack.push(idx);
                self.emit_u(OpCode::Block, idx);
            }
            Operator::Loop { blockty } => {
                let (rc, pc) = self.resolve_block_type(blockty);
                let idx = self.open_block(BlockKind::Loop, rc, pc);
                self.block_stack.push(idx);
                self.emit_u(OpCode::Loop, idx);
            }
            Operator::If { blockty } => {
                let (rc, pc) = self.resolve_block_type(blockty);
                let idx = self.open_block(BlockKind::If, rc, pc);
                self.block_stack.push(idx);
                self.emit_u(OpCode::If, idx);
            }
            Operator::Else => {
                let &idx = self
                    .block_stack
                    .last()
                    .ok_or_else(|| anyhow::anyhow!("else without open block"))?;
                self.body.blocks[idx as usize].else_pc = self.body.ops.len() as u32;
                self.emit_u(OpCode::Else, idx);
            }
            Operator::End => {
                let idx = self
                    .block_stack
                    .pop()
                    .ok_or_else(|| anyhow::anyhow!("end without open block"))?;
                self.body.blocks[idx as usize].end_pc = self.body.ops.len() as u32;
                self.emit_u(OpCode::End, idx);
            }

            Operator::Br { relative_depth } => {
                let target = self.resolve_branch_target(relative_depth);
                self.emit_u(OpCode::Br, target);
            }
            Operator::BrIf { relative_depth } => {
                let target = self.resolve_branch_target(relative_depth);
                self.emit_u(OpCode::BrIf, target);
            }
            Operator::Call { function_index } => self.emit_u(OpCode::Call, function_index),

            // --- Constants ---
            Operator::I32Const { value } => {
                self.emit_signed(OpCode::I32Const, value as i64, &value.to_le_bytes());
            }
            Operator::I64Const { value } => {
                self.emit_signed(OpCode::I64Const, value, &value.to_le_bytes());
            }
            Operator::F32Const { value } => {
                self.emit_data(OpCode::F32Const, &value.bits().to_le_bytes());
            }
            Operator::F64Const { value } => {
                self.emit_data(OpCode::F64Const, &value.bits().to_le_bytes());
            }

            // --- Locals / globals ---
            Operator::LocalGet { local_index } => self.emit_u(OpCode::LocalGet, local_index),
            Operator::LocalSet { local_index } => self.emit_u(OpCode::LocalSet, local_index),
            Operator::LocalTee { local_index } => self.emit_u(OpCode::LocalTee, local_index),
            Operator::GlobalGet { global_index } => self.emit_u(OpCode::GlobalGet, global_index),
            Operator::GlobalSet { global_index } => self.emit_u(OpCode::GlobalSet, global_index),

            // --- Stack manipulation ---
            Operator::Drop => self.emit(OpCode::Drop),
            Operator::Select => self.emit(OpCode::Select),
            Operator::TypedSelect { .. } => self.emit(OpCode::Select),

            // --- References ---
            Operator::RefNull { .. } => self.emit(OpCode::RefNull),

            // --- i32 arithmetic ---
            Operator::I32Add => self.emit(OpCode::I32Add),
            Operator::I32Sub => self.emit(OpCode::I32Sub),
            Operator::I32Mul => self.emit(OpCode::I32Mul),
            Operator::I32DivS => self.emit(OpCode::I32DivS),
            Operator::I32DivU => self.emit(OpCode::I32DivU),
            Operator::I32RemS => self.emit(OpCode::I32RemS),
            Operator::I32RemU => self.emit(OpCode::I32RemU),

            // --- i32 bitwise ---
            Operator::I32And => self.emit(OpCode::I32And),
            Operator::I32Or => self.emit(OpCode::I32Or),
            Operator::I32Xor => self.emit(OpCode::I32Xor),
            Operator::I32Shl => self.emit(OpCode::I32Shl),
            Operator::I32ShrS => self.emit(OpCode::I32ShrS),
            Operator::I32ShrU => self.emit(OpCode::I32ShrU),
            Operator::I32Rotl => self.emit(OpCode::I32Rotl),
            Operator::I32Rotr => self.emit(OpCode::I32Rotr),

            // --- i32 comparison ---
            Operator::I32Eqz => self.emit(OpCode::I32Eqz),
            Operator::I32Eq => self.emit(OpCode::I32Eq),
            Operator::I32Ne => self.emit(OpCode::I32Ne),
            Operator::I32LtS => self.emit(OpCode::I32LtS),
            Operator::I32LtU => self.emit(OpCode::I32LtU),
            Operator::I32GtS => self.emit(OpCode::I32GtS),
            Operator::I32GtU => self.emit(OpCode::I32GtU),
            Operator::I32LeS => self.emit(OpCode::I32LeS),
            Operator::I32LeU => self.emit(OpCode::I32LeU),
            Operator::I32GeS => self.emit(OpCode::I32GeS),
            Operator::I32GeU => self.emit(OpCode::I32GeU),

            // --- i32 unary ---
            Operator::I32Clz => self.emit(OpCode::I32Clz),
            Operator::I32Ctz => self.emit(OpCode::I32Ctz),
            Operator::I32Popcnt => self.emit(OpCode::I32Popcnt),

            // --- i32 conversion ---
            Operator::I32WrapI64 => self.emit(OpCode::I32WrapI64),
            Operator::I32Extend8S => self.emit(OpCode::I32Extend8S),
            Operator::I32Extend16S => self.emit(OpCode::I32Extend16S),
            Operator::I32TruncF32S => self.emit(OpCode::I32TruncF32S),
            Operator::I32TruncF32U => self.emit(OpCode::I32TruncF32U),
            Operator::I32TruncF64S => self.emit(OpCode::I32TruncF64S),
            Operator::I32TruncF64U => self.emit(OpCode::I32TruncF64U),
            Operator::I32TruncSatF32S => self.emit(OpCode::I32TruncSatF32S),
            Operator::I32TruncSatF32U => self.emit(OpCode::I32TruncSatF32U),
            Operator::I32TruncSatF64S => self.emit(OpCode::I32TruncSatF64S),
            Operator::I32TruncSatF64U => self.emit(OpCode::I32TruncSatF64U),
            Operator::I32ReinterpretF32 => self.emit(OpCode::I32ReinterpretF32),

            // --- i64 arithmetic ---
            Operator::I64Add => self.emit(OpCode::I64Add),
            Operator::I64Sub => self.emit(OpCode::I64Sub),
            Operator::I64Mul => self.emit(OpCode::I64Mul),
            Operator::I64DivS => self.emit(OpCode::I64DivS),
            Operator::I64DivU => self.emit(OpCode::I64DivU),
            Operator::I64RemS => self.emit(OpCode::I64RemS),
            Operator::I64RemU => self.emit(OpCode::I64RemU),

            // --- i64 bitwise ---
            Operator::I64And => self.emit(OpCode::I64And),
            Operator::I64Or => self.emit(OpCode::I64Or),
            Operator::I64Xor => self.emit(OpCode::I64Xor),
            Operator::I64Shl => self.emit(OpCode::I64Shl),
            Operator::I64ShrS => self.emit(OpCode::I64ShrS),
            Operator::I64ShrU => self.emit(OpCode::I64ShrU),
            Operator::I64Rotl => self.emit(OpCode::I64Rotl),
            Operator::I64Rotr => self.emit(OpCode::I64Rotr),

            // --- i64 comparison ---
            Operator::I64Eqz => self.emit(OpCode::I64Eqz),
            Operator::I64Eq => self.emit(OpCode::I64Eq),
            Operator::I64Ne => self.emit(OpCode::I64Ne),
            Operator::I64LtS => self.emit(OpCode::I64LtS),
            Operator::I64LtU => self.emit(OpCode::I64LtU),
            Operator::I64GtS => self.emit(OpCode::I64GtS),
            Operator::I64GtU => self.emit(OpCode::I64GtU),
            Operator::I64LeS => self.emit(OpCode::I64LeS),
            Operator::I64LeU => self.emit(OpCode::I64LeU),
            Operator::I64GeS => self.emit(OpCode::I64GeS),
            Operator::I64GeU => self.emit(OpCode::I64GeU),

            // --- i64 unary ---
            Operator::I64Clz => self.emit(OpCode::I64Clz),
            Operator::I64Ctz => self.emit(OpCode::I64Ctz),
            Operator::I64Popcnt => self.emit(OpCode::I64Popcnt),

            // --- i64 conversion ---
            Operator::I64ExtendI32S => self.emit(OpCode::I64ExtendI32S),
            Operator::I64ExtendI32U => self.emit(OpCode::I64ExtendI32U),
            Operator::I64Extend8S => self.emit(OpCode::I64Extend8S),
            Operator::I64Extend16S => self.emit(OpCode::I64Extend16S),
            Operator::I64Extend32S => self.emit(OpCode::I64Extend32S),
            Operator::I64TruncF32S => self.emit(OpCode::I64TruncF32S),
            Operator::I64TruncF32U => self.emit(OpCode::I64TruncF32U),
            Operator::I64TruncF64S => self.emit(OpCode::I64TruncF64S),
            Operator::I64TruncF64U => self.emit(OpCode::I64TruncF64U),
            Operator::I64TruncSatF32S => self.emit(OpCode::I64TruncSatF32S),
            Operator::I64TruncSatF32U => self.emit(OpCode::I64TruncSatF32U),
            Operator::I64TruncSatF64S => self.emit(OpCode::I64TruncSatF64S),
            Operator::I64TruncSatF64U => self.emit(OpCode::I64TruncSatF64U),
            Operator::I64ReinterpretF64 => self.emit(OpCode::I64ReinterpretF64),

            // --- f32 arithmetic ---
            Operator::F32Add => self.emit(OpCode::F32Add),
            Operator::F32Sub => self.emit(OpCode::F32Sub),
            Operator::F32Mul => self.emit(OpCode::F32Mul),
            Operator::F32Div => self.emit(OpCode::F32Div),
            Operator::F32Min => self.emit(OpCode::F32Min),
            Operator::F32Max => self.emit(OpCode::F32Max),
            Operator::F32Copysign => self.emit(OpCode::F32Copysign),

            // --- f32 unary ---
            Operator::F32Abs => self.emit(OpCode::F32Abs),
            Operator::F32Neg => self.emit(OpCode::F32Neg),
            Operator::F32Sqrt => self.emit(OpCode::F32Sqrt),
            Operator::F32Ceil => self.emit(OpCode::F32Ceil),
            Operator::F32Floor => self.emit(OpCode::F32Floor),
            Operator::F32Trunc => self.emit(OpCode::F32Trunc),
            Operator::F32Nearest => self.emit(OpCode::F32Nearest),

            // --- f32 comparison ---
            Operator::F32Eq => self.emit(OpCode::F32Eq),
            Operator::F32Ne => self.emit(OpCode::F32Ne),
            Operator::F32Lt => self.emit(OpCode::F32Lt),
            Operator::F32Gt => self.emit(OpCode::F32Gt),
            Operator::F32Le => self.emit(OpCode::F32Le),
            Operator::F32Ge => self.emit(OpCode::F32Ge),

            // --- f32 conversion ---
            Operator::F32ConvertI32S => self.emit(OpCode::F32ConvertI32S),
            Operator::F32ConvertI32U => self.emit(OpCode::F32ConvertI32U),
            Operator::F32ConvertI64S => self.emit(OpCode::F32ConvertI64S),
            Operator::F32ConvertI64U => self.emit(OpCode::F32ConvertI64U),
            Operator::F32DemoteF64 => self.emit(OpCode::F32DemoteF64),
            Operator::F32ReinterpretI32 => self.emit(OpCode::F32ReinterpretI32),

            // --- f64 arithmetic ---
            Operator::F64Add => self.emit(OpCode::F64Add),
            Operator::F64Sub => self.emit(OpCode::F64Sub),
            Operator::F64Mul => self.emit(OpCode::F64Mul),
            Operator::F64Div => self.emit(OpCode::F64Div),
            Operator::F64Min => self.emit(OpCode::F64Min),
            Operator::F64Max => self.emit(OpCode::F64Max),
            Operator::F64Copysign => self.emit(OpCode::F64Copysign),

            // --- f64 unary ---
            Operator::F64Abs => self.emit(OpCode::F64Abs),
            Operator::F64Neg => self.emit(OpCode::F64Neg),
            Operator::F64Sqrt => self.emit(OpCode::F64Sqrt),
            Operator::F64Ceil => self.emit(OpCode::F64Ceil),
            Operator::F64Floor => self.emit(OpCode::F64Floor),
            Operator::F64Trunc => self.emit(OpCode::F64Trunc),
            Operator::F64Nearest => self.emit(OpCode::F64Nearest),

            // --- f64 comparison ---
            Operator::F64Eq => self.emit(OpCode::F64Eq),
            Operator::F64Ne => self.emit(OpCode::F64Ne),
            Operator::F64Lt => self.emit(OpCode::F64Lt),
            Operator::F64Gt => self.emit(OpCode::F64Gt),
            Operator::F64Le => self.emit(OpCode::F64Le),
            Operator::F64Ge => self.emit(OpCode::F64Ge),

            // --- f64 conversion ---
            Operator::F64ConvertI32S => self.emit(OpCode::F64ConvertI32S),
            Operator::F64ConvertI32U => self.emit(OpCode::F64ConvertI32U),
            Operator::F64ConvertI64S => self.emit(OpCode::F64ConvertI64S),
            Operator::F64ConvertI64U => self.emit(OpCode::F64ConvertI64U),
            Operator::F64PromoteF32 => self.emit(OpCode::F64PromoteF32),
            Operator::F64ReinterpretI64 => self.emit(OpCode::F64ReinterpretI64),

            // Unsupported opcodes trap cleanly.
            _ => self.emit(OpCode::Unreachable),
        }
        Ok(())
    }

    // --- Emit helpers ---

    fn emit(&mut self, opcode: OpCode) {
        self.body.ops.push(pack(opcode));
    }

    /// Emit an unsigned immediate, inlining if it fits in 24 bits.
    fn emit_u(&mut self, opcode: OpCode, value: u32) {
        if fits_imm24_unsigned(value as u64) {
            self.body.ops.push(pack_imm_u(opcode, value));
        } else {
            self.emit_data(opcode, &value.to_le_bytes());
        }
    }

    /// Emit a signed immediate, inlining if it fits in 24 bits.
    fn emit_signed(&mut self, opcode: OpCode, value: i64, full_bytes: &[u8]) {
        if fits_imm24(value) {
            self.body.ops.push(pack_imm(opcode, value as i32));
        } else {
            self.emit_data(opcode, full_bytes);
        }
    }

    /// Spill to the data side table via a `DataStream` reference.
    fn emit_data(&mut self, opcode: OpCode, bytes: &[u8]) {
        let offset = self.body.data.len() as u32;
        debug_assert!(fits_imm24_unsigned(offset as u64), "data offset overflow");
        self.body.ops.push(pack_imm_u(OpCode::DataStream, offset));
        self.body.data.push(opcode as u8);
        self.body.data.extend_from_slice(bytes);
    }
}
