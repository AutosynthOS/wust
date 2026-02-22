use wasmparser::{FunctionBody, Operator};
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

    // --- i32 comparison (no immediate) ---
    I32LeS,

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
    InlineOp(
        (opcode as u64)
            | ((a as u64) << 8)
            | (((val as u16) as u64) << 16),
    )
}

/// Pack opcode + u16 in bits[8..24] + u8 in bits[24..32].
fn pack_u16_u8(opcode: OpCode, a: u16, b: u8) -> InlineOp {
    InlineOp(
        (opcode as u64)
            | ((a as u64) << 8)
            | ((b as u64) << 24),
    )
}

/// Pack opcode + u8 in bits[8..16] + u8 in bits[16..24].
fn pack_two_u8(opcode: OpCode, a: u8, b: u8) -> InlineOp {
    InlineOp((opcode as u64) | ((a as u64) << 8) | ((b as u64) << 16))
}

/// Pack opcode + three u8 fields in bits[8..16], [16..24], [24..32].
fn pack_three_u8(opcode: OpCode, a: u8, b: u8, c: u8) -> InlineOp {
    InlineOp(
        (opcode as u64)
            | ((a as u64) << 8)
            | ((b as u64) << 16)
            | ((c as u64) << 24),
    )
}

fn fits_imm24(val: i64) -> bool {
    val >= IMM24_MIN as i64 && val <= IMM24_MAX as i64
}

fn fits_imm24_unsigned(val: u64) -> bool {
    val <= IMM24_MASK as u64
}

impl ParsedBody {
    /// Parse raw wasm function body bytes into a pre-decoded body.
    pub(crate) fn parse(reader: &FunctionBody) -> Result<Self, anyhow::Error> {
        let mut body = Self::empty();

        // Implicit function-level block (index 0).
        let func_block_idx = body.open_block(BlockKind::Function);

        let ops_reader = reader.get_operators_reader()?;
        // Track open block indices so `end` can find the right one.
        let mut block_stack: Vec<u32> = vec![func_block_idx];

        for op in ops_reader {
            body.parse_op(op?, &mut block_stack)?;
        }
        body.fuse();
        Ok(body)
    }

    /// Allocate a new block entry, returning its index.
    fn open_block(&mut self, kind: BlockKind) -> u32 {
        let idx = self.blocks.len() as u32;
        self.blocks.push(Block {
            kind,
            start_pc: self.ops.len() as u32,
            end_pc: 0,
            else_pc: 0,
        });
        idx
    }

    fn parse_op(
        &mut self,
        op: Operator,
        block_stack: &mut Vec<u32>,
    ) -> Result<(), anyhow::Error> {
        match op {
            // No-immediate ops
            Operator::Nop => self.ops.push(pack(OpCode::Nop)),
            Operator::Unreachable => self.ops.push(pack(OpCode::Unreachable)),
            Operator::Return => self.ops.push(pack(OpCode::Return)),

            // Block control flow
            Operator::Block { .. } => {
                let idx = self.open_block(BlockKind::Block);
                block_stack.push(idx);
                self.ops.push(pack_imm_u(OpCode::Block, idx));
            }
            Operator::Loop { .. } => {
                let idx = self.open_block(BlockKind::Loop);
                block_stack.push(idx);
                self.ops.push(pack_imm_u(OpCode::Loop, idx));
            }
            Operator::If { .. } => {
                let idx = self.open_block(BlockKind::If);
                block_stack.push(idx);
                self.ops.push(pack_imm_u(OpCode::If, idx));
            }
            Operator::Else => {
                let &idx = block_stack.last().expect("else without open block");
                self.blocks[idx as usize].else_pc = self.ops.len() as u32;
                self.ops.push(pack_imm_u(OpCode::Else, idx));
            }
            Operator::End => {
                let idx = block_stack.pop().expect("end without open block");
                self.blocks[idx as usize].end_pc = self.ops.len() as u32;
                self.ops.push(pack_imm_u(OpCode::End, idx));
            }

            // i32 arithmetic
            Operator::I32Add => self.ops.push(pack(OpCode::I32Add)),
            Operator::I32Sub => self.ops.push(pack(OpCode::I32Sub)),

            // i32 comparison
            Operator::I32LeS => self.ops.push(pack(OpCode::I32LeS)),

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

            // Globals
            Operator::GlobalGet { global_index } => {
                self.emit_unsigned(OpCode::GlobalGet, global_index);
            }
            Operator::GlobalSet { global_index } => {
                self.emit_unsigned(OpCode::GlobalSet, global_index);
            }

            // Call
            Operator::Call { function_index } => {
                self.emit_unsigned(OpCode::Call, function_index);
            }

            _ => {} // Unknown ops skipped for now.
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
                    return Some((
                        pack_imm_u(OpCode::LocalGetReturn, local),
                        2,
                    ));
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
        ParsedBody {
            ops: Vec::new(),
            data: Vec::new(),
            blocks: Vec::new(),
        }
    }
}
