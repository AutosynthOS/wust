use bilge::prelude::*;
use wasmparser::{FunctionBody, Operator};

/// A parsed function body, pre-decoded from raw wasm bytes.
#[derive(Debug, Clone)]
pub(crate) struct ParsedBody {
    /// Op table: one u32 per instruction.
    ///
    /// ```text
    /// [ opcode: 8 bits ][ immediate: 24 bits ]
    /// ```
    ///
    /// When opcode = `DataStream`, the immediate is a byte offset
    /// into `data` where the full instruction is stored.
    pub(crate) ops: Vec<InlineOp>,

    /// Data stream for instructions that don't fit inline.
    pub(crate) data: Vec<u8>,

    /// Block metadata, indexed by block index.
    pub(crate) blocks: Vec<Block>,
}

/// An instruction packed into 32 bits: 8-bit opcode + 24-bit immediate.
#[bitsize(32)]
#[derive(FromBits, DebugBits, Clone, Copy)]
pub(crate) struct InlineOp {
    pub immediate: u24,
    pub opcode: OpCode,
}

/// Flat opcode — 8 bits, up to 256 instruction types.
///
/// Variant 0 (`DataStream`) means the immediate is a data stream
/// offset. All other variants are directly executable opcodes.
#[bitsize(8)]
#[derive(FromBits, Debug, Clone, Copy, PartialEq)]
pub(crate) enum OpCode {
    // --- Data stream (opcode = 0) ---
    DataStream,

    // --- No-immediate operations ---
    Nop,
    Unreachable,
    End,
    Return,

    // --- i32 arithmetic (no immediate) ---
    I32Add,
    I32Sub,

    // --- Operations with immediates ---
    I32Const, // imm = sign-extended 24-bit value
    I64Const, // imm = sign-extended 24-bit value

    LocalGet, // imm = local index
    LocalSet, // imm = local index
    LocalTee, // imm = local index

    GlobalGet, // imm = global index
    GlobalSet, // imm = global index

    Call, // imm = function index

    Block, // imm = block metadata index
    Loop,  // imm = block metadata index
    If,    // imm = block metadata index
    Else,  // imm = block metadata index
    Br,    // imm = block target
    BrIf,  // imm = block target

    #[fallback]
    ReservedUnknown(u8),
}

/// Metadata for a block/loop/if, resolved at parse time.
#[derive(Debug, Clone)]
pub(crate) struct Block {
    pub(crate) kind: BlockKind,
    /// PC (op table index) to jump to on `br`.
    pub(crate) br_target: u32,
}

#[derive(Debug, Clone)]
pub(crate) enum BlockKind {
    Block,
    Loop,
    If,
}

const IMM24_MAX: i32 = (1 << 23) - 1;
const IMM24_MIN: i32 = -(1 << 23);
const IMM24_MASK: u32 = 0x00FF_FFFF;

/// Pack an opcode with no immediate.
fn pack(opcode: OpCode) -> InlineOp {
    InlineOp::new(u24::new(0), opcode)
}

/// Pack an opcode with a 24-bit immediate.
fn pack_imm(opcode: OpCode, imm: i32) -> InlineOp {
    debug_assert!(imm >= IMM24_MIN && imm <= IMM24_MAX);
    InlineOp::new(u24::new((imm as u32) & IMM24_MASK), opcode)
}

/// Pack an opcode with an unsigned 24-bit immediate.
fn pack_imm_u(opcode: OpCode, imm: u32) -> InlineOp {
    debug_assert!(imm <= IMM24_MASK);
    InlineOp::new(u24::new(imm), opcode)
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
        let ops_reader = reader.get_operators_reader()?;
        for op in ops_reader {
            body.parse_op(op?)?;
        }
        Ok(body)
    }

    fn parse_op(&mut self, op: Operator) -> Result<(), anyhow::Error> {
        match op {
            // No-immediate ops
            Operator::Nop => self.ops.push(pack(OpCode::Nop)),
            Operator::Unreachable => self.ops.push(pack(OpCode::Unreachable)),
            Operator::End => self.ops.push(pack(OpCode::End)),
            Operator::Return => self.ops.push(pack(OpCode::Return)),

            // i32 arithmetic
            Operator::I32Add => self.ops.push(pack(OpCode::I32Add)),
            Operator::I32Sub => self.ops.push(pack(OpCode::I32Sub)),

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
        self.data.push(u8::from(opcode));
        self.data.extend_from_slice(bytes);
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

#[cfg(test)]
mod tests {
    use super::*;

    fn decode(op: InlineOp) -> (OpCode, u32) {
        (op.opcode(), op.immediate().value())
    }

    #[test]
    fn no_immediate_ops() {
        let cases = [
            (OpCode::Nop, pack(OpCode::Nop)),
            (OpCode::Unreachable, pack(OpCode::Unreachable)),
            (OpCode::End, pack(OpCode::End)),
            (OpCode::Return, pack(OpCode::Return)),
            (OpCode::I32Add, pack(OpCode::I32Add)),
            (OpCode::I32Sub, pack(OpCode::I32Sub)),
        ];
        for (expected_opcode, packed) in cases {
            let (opcode, imm) = decode(packed);
            assert_eq!(opcode, expected_opcode);
            assert_eq!(imm, 0);
        }
    }

    #[test]
    fn signed_positive_immediate() {
        let packed = pack_imm(OpCode::I32Const, 42);
        let (opcode, imm) = decode(packed);
        assert_eq!(opcode, OpCode::I32Const);
        assert_eq!(imm, 42);
    }

    #[test]
    fn signed_negative_immediate() {
        let packed = pack_imm(OpCode::I32Const, -1);
        let (opcode, imm) = decode(packed);
        assert_eq!(opcode, OpCode::I32Const);
        // Raw bits: 0x00FFFFFF. Sign-extend from 24 bits:
        assert_eq!(imm, 0x00FF_FFFF);
        let sign_extended = (imm as i32) << 8 >> 8;
        assert_eq!(sign_extended, -1);
    }

    #[test]
    fn unsigned_immediate() {
        let packed = pack_imm_u(OpCode::LocalGet, 5);
        let (opcode, imm) = decode(packed);
        assert_eq!(opcode, OpCode::LocalGet);
        assert_eq!(imm, 5);
    }

    #[test]
    fn call_function_index() {
        let packed = pack_imm_u(OpCode::Call, 100);
        let (opcode, imm) = decode(packed);
        assert_eq!(opcode, OpCode::Call);
        assert_eq!(imm, 100);
    }

    #[test]
    fn large_const_spills_to_data() {
        let mut body = ParsedBody::empty();
        let big: i64 = 1 << 24;
        body.emit_signed(OpCode::I32Const, big, &(big as i32).to_le_bytes());
        let (opcode, offset) = decode(body.ops[0]);
        assert_eq!(opcode, OpCode::DataStream);
        assert_eq!(offset, 0); // First entry in data stream.
        // Data stream: [opcode_byte, 4 bytes LE]
        assert_eq!(body.data.len(), 5);
        assert_eq!(body.data[0], u8::from(OpCode::I32Const));
    }

    #[test]
    fn imm24_boundary_values() {
        // Max positive
        let packed = pack_imm(OpCode::I32Const, IMM24_MAX);
        let (_, imm) = decode(packed);
        assert_eq!(imm, IMM24_MAX as u32);

        // Min negative
        let packed = pack_imm(OpCode::I64Const, IMM24_MIN);
        let (_, imm) = decode(packed);
        let sign_extended = (imm as i32) << 8 >> 8;
        assert_eq!(sign_extended, IMM24_MIN);
    }
}
