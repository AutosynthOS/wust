//! Engine-specific peephole fusion pass.
//!
//! Rewrites sequences of `InlineOp`s into fused opcodes that give
//! the JIT compiler better context for register allocation and
//! immediate operand usage. The fused opcodes use raw byte values
//! ≥128, outside the range of `wust_core::OpCode` variants.

use wust_core::module::body::{Block, ParsedBody};
use wust_core::module::op::{InlineOp, OpCode};

// --- Fused opcode constants (≥128, outside wust_core::OpCode range) ---

/// First fused opcode value. Must be above the highest `OpCode` discriminant.
pub(crate) const FUSED_BASE: u8 = 192;

pub(crate) const LOCAL_GET_I32_CONST_LE_S_IF: u8 = FUSED_BASE;
pub(crate) const LOCAL_GET_I32_CONST_SUB: u8 = FUSED_BASE + 1;
pub(crate) const LOCAL_GET_I32_CONST_ADD: u8 = FUSED_BASE + 2;
pub(crate) const LOCAL_GET_I32_EQZ_IF: u8 = FUSED_BASE + 3;
pub(crate) const LOCAL_GET_LOCAL_GET_ADD: u8 = FUSED_BASE + 4;
pub(crate) const CALL_LOCAL_SET: u8 = FUSED_BASE + 5;
pub(crate) const LOCAL_GET_RETURN: u8 = FUSED_BASE + 6;

// --- Packing helpers ---

/// Pack a fused opcode + u8 in bits[8..16] + i16 in bits[16..32].
fn pack_u8_i16(opcode: u8, a: u8, val: i16) -> InlineOp {
    InlineOp::from_raw((opcode as u64) | ((a as u64) << 8) | (((val as u16) as u64) << 16))
}

/// Pack a fused opcode + u16 in bits[8..24] + u8 in bits[24..32].
fn pack_u16_u8(opcode: u8, a: u16, b: u8) -> InlineOp {
    InlineOp::from_raw((opcode as u64) | ((a as u64) << 8) | ((b as u64) << 24))
}

/// Pack a fused opcode + u8 in bits[8..16] + u8 in bits[16..24].
fn pack_two_u8(opcode: u8, a: u8, b: u8) -> InlineOp {
    InlineOp::from_raw((opcode as u64) | ((a as u64) << 8) | ((b as u64) << 16))
}

/// Pack a fused opcode + three u8 fields.
fn pack_three_u8(opcode: u8, a: u8, b: u8, c: u8) -> InlineOp {
    InlineOp::from_raw(
        (opcode as u64) | ((a as u64) << 8) | ((b as u64) << 16) | ((c as u64) << 24),
    )
}

/// Pack a fused opcode + unsigned immediate in bits[8..32].
fn pack_imm_u(opcode: u8, imm: u32) -> InlineOp {
    InlineOp::from_raw(((imm as u64) << 8) | (opcode as u64))
}

/// Result of the peephole fusion pass.
pub(crate) struct FuseResult {
    pub ops: Vec<InlineOp>,
    pub blocks: Vec<Block>,
    /// For each fused op index, the original (unfused) PC of the last
    /// instruction in the fused group. Used to write the correct wasm PC
    /// into frame headers at suspend points.
    pub original_pc: Vec<u32>,
}

/// Run the peephole fusion pass on a parsed body.
///
/// Returns fused ops, remapped blocks, and a reverse PC map (fused → original).
pub(crate) fn fuse(body: &ParsedBody) -> FuseResult {
    let old_ops = &body.ops;
    let len = old_ops.len();
    let mut new_ops = Vec::with_capacity(len);
    let mut original_pc = Vec::with_capacity(len);
    let mut pc_map: Vec<u32> = vec![0; len + 1];
    let mut i = 0;

    while i < len {
        pc_map[i] = new_ops.len() as u32;
        if let Some((op, consumed)) = try_fuse_at(old_ops, i, len) {
            original_pc.push((i + consumed - 1) as u32);
            new_ops.push(op);
            for j in 1..consumed {
                pc_map[i + j] = pc_map[i];
            }
            i += consumed;
        } else {
            original_pc.push(i as u32);
            new_ops.push(old_ops[i]);
            i += 1;
        }
    }
    pc_map[len] = new_ops.len() as u32;

    let mut blocks = body.blocks.clone();
    remap_blocks(&mut blocks, &pc_map);
    FuseResult { ops: new_ops, blocks, original_pc }
}

fn try_fuse_at(ops: &[InlineOp], i: usize, len: usize) -> Option<(InlineOp, usize)> {
    let remaining = len - i;

    // 4-op: local.get + i32.const + i32.le_s + if
    if remaining >= 4 {
        let (o0, o1, o2, o3) = (ops[i], ops[i + 1], ops[i + 2], ops[i + 3]);
        if o0.opcode() == OpCode::LocalGetI32
            && o1.opcode() == OpCode::I32Const
            && o2.opcode() == OpCode::I32LeS
            && o3.opcode() == OpCode::If
        {
            let local = o0.local_index() as u32;
            let konst = (o1.immediate_u32() as i32) << 8 >> 8;
            let block = o3.immediate_u32();
            if local < 256 && konst >= i8::MIN as i32 && konst <= i8::MAX as i32 && block < 256 {
                return Some((
                    pack_three_u8(LOCAL_GET_I32_CONST_LE_S_IF, local as u8, konst as u8, block as u8),
                    4,
                ));
            }
        }
    }

    // 3-op fusions
    if remaining >= 3 {
        let (o0, o1, o2) = (ops[i], ops[i + 1], ops[i + 2]);

        // local.get + i32.const + i32.sub
        if o0.opcode() == OpCode::LocalGetI32
            && o1.opcode() == OpCode::I32Const
            && o2.opcode() == OpCode::I32Sub
        {
            let local = o0.local_index() as u32;
            let konst = (o1.immediate_u32() as i32) << 8 >> 8;
            if local < 256 && konst >= i16::MIN as i32 && konst <= i16::MAX as i32 {
                return Some((
                    pack_u8_i16(LOCAL_GET_I32_CONST_SUB, local as u8, konst as i16),
                    3,
                ));
            }
        }

        // local.get + i32.const + i32.add
        if o0.opcode() == OpCode::LocalGetI32
            && o1.opcode() == OpCode::I32Const
            && o2.opcode() == OpCode::I32Add
        {
            let local = o0.local_index() as u32;
            let konst = (o1.immediate_u32() as i32) << 8 >> 8;
            if local < 256 && konst >= i16::MIN as i32 && konst <= i16::MAX as i32 {
                return Some((
                    pack_u8_i16(LOCAL_GET_I32_CONST_ADD, local as u8, konst as i16),
                    3,
                ));
            }
        }

        // local.get + i32.eqz + if
        if o0.opcode() == OpCode::LocalGetI32
            && o1.opcode() == OpCode::I32Eqz
            && o2.opcode() == OpCode::If
        {
            let local = o0.local_index() as u32;
            let block = o2.immediate_u32();
            if local < 256 && block < 256 {
                return Some((
                    pack_two_u8(LOCAL_GET_I32_EQZ_IF, local as u8, block as u8),
                    3,
                ));
            }
        }

        // local.get + local.get + i32.add
        if o0.opcode() == OpCode::LocalGetI32
            && o1.opcode() == OpCode::LocalGetI32
            && o2.opcode() == OpCode::I32Add
        {
            let a = o0.local_index() as u32;
            let b = o1.local_index() as u32;
            if a < 256 && b < 256 {
                return Some((
                    pack_two_u8(LOCAL_GET_LOCAL_GET_ADD, a as u8, b as u8),
                    3,
                ));
            }
        }
    }

    // 2-op fusions
    if remaining >= 2 {
        let (o0, o1) = (ops[i], ops[i + 1]);

        // call + local.set
        if o0.opcode() == OpCode::Call && o1.opcode() == OpCode::LocalSetI32 {
            let func = o0.immediate_u32();
            let local = o1.local_index() as u32;
            if func < 65536 && local < 256 {
                return Some((pack_u16_u8(CALL_LOCAL_SET, func as u16, local as u8), 2));
            }
        }

        // local.get + return
        if o0.opcode() == OpCode::LocalGetI32 && o1.opcode() == OpCode::Return {
            let local = o0.local_index() as u32;
            if local < 256 {
                return Some((pack_imm_u(LOCAL_GET_RETURN, local), 2));
            }
        }
    }

    None
}

fn remap_blocks(blocks: &mut [Block], pc_map: &[u32]) {
    for block in blocks {
        block.start_pc = pc_map[block.start_pc as usize];
        block.end_pc = pc_map[block.end_pc as usize];
        if block.else_pc != 0 {
            block.else_pc = pc_map[block.else_pc as usize];
        }
    }
}

/// Fuel cost for an opcode byte. Handles both standard and fused opcodes.
pub(crate) fn fuel_cost(raw: u8) -> u32 {
    match raw {
        // Fused opcodes: sum of constituent fuel costs.
        LOCAL_GET_I32_CONST_LE_S_IF => 2, // le_s=0, if=2
        LOCAL_GET_I32_CONST_SUB => 1,     // get+const=0, sub=1
        LOCAL_GET_I32_CONST_ADD => 1,     // get+const=0, add=1
        LOCAL_GET_I32_EQZ_IF => 2,        // eqz=0, if=2
        LOCAL_GET_LOCAL_GET_ADD => 1,     // gets=0, add=1
        CALL_LOCAL_SET => 1,              // call=1, set=0
        LOCAL_GET_RETURN => 1,            // get=0, return=1
        // Standard opcodes: delegate to OpCode.
        _ => {
            // SAFETY: raw < FUSED_BASE is a valid OpCode discriminant.
            let op: OpCode = unsafe { std::mem::transmute(raw) };
            op.fuel_cost()
        }
    }
}

/// Human-readable label for a fused opcode, or None if not fused.
pub(crate) fn display_label(op: InlineOp) -> Option<String> {
    let raw = op.raw_opcode();
    Some(match raw {
        LOCAL_GET_I32_CONST_SUB => {
            let local = op.imm_u8_a();
            let konst = op.imm_i16_hi();
            format!("sub(local.get {local}, {konst})")
        }
        LOCAL_GET_I32_CONST_ADD => {
            let local = op.imm_u8_a();
            let konst = op.imm_i16_hi();
            format!("add(local.get {local}, {konst})")
        }
        LOCAL_GET_I32_CONST_LE_S_IF => {
            let local = op.imm_u8_a();
            let konst = op.imm_u8_b() as i8;
            format!("if le_s(local.get {local}, {konst})")
        }
        LOCAL_GET_I32_EQZ_IF => {
            let local = op.imm_u8_a();
            format!("if eqz(local.get {local})")
        }
        LOCAL_GET_LOCAL_GET_ADD => {
            let a = op.imm_u8_a();
            let b = op.imm_u8_b();
            format!("add(local.get {a}, local.get {b})")
        }
        CALL_LOCAL_SET => {
            let func = op.imm_u16_lo();
            let local = op.imm_u8_c();
            format!("call {func} -> local.set {local}")
        }
        LOCAL_GET_RETURN => {
            let local = op.imm_u8_a();
            format!("return local.get {local}")
        }
        _ => return None,
    })
}
