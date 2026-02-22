use super::*;

fn decode(op: InlineOp) -> (OpCode, u32) {
    (op.opcode(), op.immediate_u32())
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
    assert_eq!(offset, 0);
    // Data stream: [opcode_byte, 4 bytes LE]
    assert_eq!(body.data.len(), 5);
    assert_eq!(body.data[0], OpCode::I32Const as u8);
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

#[test]
fn superinstruction_packing_roundtrips() {
    // pack_u8_i16: local(8) + const_i16(16)
    let op = pack_u8_i16(OpCode::LocalGetI32ConstSub, 3, -5);
    assert_eq!(op.opcode(), OpCode::LocalGetI32ConstSub);
    assert_eq!(op.imm_u8_a(), 3);
    assert_eq!(op.imm_i16_hi(), -5);

    // pack_u8_i16 with positive value
    let op = pack_u8_i16(OpCode::LocalGetI32ConstAdd, 0, 100);
    assert_eq!(op.opcode(), OpCode::LocalGetI32ConstAdd);
    assert_eq!(op.imm_u8_a(), 0);
    assert_eq!(op.imm_i16_hi(), 100);

    // pack_u16_u8: func(16) + local(8)
    let op = pack_u16_u8(OpCode::CallLocalSet, 1000, 5);
    assert_eq!(op.opcode(), OpCode::CallLocalSet);
    assert_eq!(op.imm_u16_lo(), 1000);
    assert_eq!(op.imm_u8_c(), 5);

    // pack_two_u8: localA(8) + localB(8)
    let op = pack_two_u8(OpCode::LocalGetLocalGetAdd, 1, 2);
    assert_eq!(op.opcode(), OpCode::LocalGetLocalGetAdd);
    assert_eq!(op.imm_u8_a(), 1);
    assert_eq!(op.imm_u8_b(), 2);

    // pack_three_u8: local(8) + const(8) + block(8)
    let op = pack_three_u8(OpCode::LocalGetI32ConstLeSIf, 0, 1, 7);
    assert_eq!(op.opcode(), OpCode::LocalGetI32ConstLeSIf);
    assert_eq!(op.imm_u8_a(), 0);
    assert_eq!(op.imm_u8_b(), 1);
    assert_eq!(op.imm_u8_c(), 7);
}

#[test]
fn fuse_local_get_return() {
    let mut body = ParsedBody::empty();
    body.ops.push(pack_imm_u(OpCode::LocalGet, 2));
    body.ops.push(pack(OpCode::Return));
    body.fuse();
    assert_eq!(body.ops.len(), 1);
    assert_eq!(body.ops[0].opcode(), OpCode::LocalGetReturn);
    assert_eq!(body.ops[0].imm_u8_a(), 2);
}

#[test]
fn fuse_local_get_const_sub() {
    let mut body = ParsedBody::empty();
    body.ops.push(pack_imm_u(OpCode::LocalGet, 0));
    body.ops.push(pack_imm(OpCode::I32Const, 1));
    body.ops.push(pack(OpCode::I32Sub));
    body.fuse();
    assert_eq!(body.ops.len(), 1);
    assert_eq!(body.ops[0].opcode(), OpCode::LocalGetI32ConstSub);
    assert_eq!(body.ops[0].imm_u8_a(), 0);
    assert_eq!(body.ops[0].imm_i16_hi(), 1);
}

#[test]
fn fuse_call_local_set() {
    let mut body = ParsedBody::empty();
    body.ops.push(pack_imm_u(OpCode::Call, 42));
    body.ops.push(pack_imm_u(OpCode::LocalSet, 3));
    body.fuse();
    assert_eq!(body.ops.len(), 1);
    assert_eq!(body.ops[0].opcode(), OpCode::CallLocalSet);
    assert_eq!(body.ops[0].imm_u16_lo(), 42);
    assert_eq!(body.ops[0].imm_u8_c(), 3);
}

#[test]
fn fuse_local_get_local_get_add() {
    let mut body = ParsedBody::empty();
    body.ops.push(pack_imm_u(OpCode::LocalGet, 1));
    body.ops.push(pack_imm_u(OpCode::LocalGet, 2));
    body.ops.push(pack(OpCode::I32Add));
    body.fuse();
    assert_eq!(body.ops.len(), 1);
    assert_eq!(body.ops[0].opcode(), OpCode::LocalGetLocalGetAdd);
    assert_eq!(body.ops[0].imm_u8_a(), 1);
    assert_eq!(body.ops[0].imm_u8_b(), 2);
}

/// Simulate the fib function's op sequence and verify fusion
/// reduces 21 ops down to the expected fused sequence.
#[test]
fn fuse_fib_sequence() {
    let mut body = ParsedBody::empty();

    // Block 0: implicit function block (added by parser normally).
    // Block 1: the if block.
    body.blocks.push(Block {
        kind: BlockKind::Function,
        start_pc: 0,
        end_pc: 20, // will be remapped
        else_pc: 0,
    });
    body.blocks.push(Block {
        kind: BlockKind::If,
        start_pc: 3, // the If instruction
        end_pc: 6,   // the End(1) instruction
        else_pc: 0,  // no else branch — uses end as else target
    });

    // 0: local.get 0
    body.ops.push(pack_imm_u(OpCode::LocalGet, 0));
    // 1: i32.const 1
    body.ops.push(pack_imm(OpCode::I32Const, 1));
    // 2: i32.le_s
    body.ops.push(pack(OpCode::I32LeS));
    // 3: if (block 1)
    body.ops.push(pack_imm_u(OpCode::If, 1));
    // 4: local.get 0
    body.ops.push(pack_imm_u(OpCode::LocalGet, 0));
    // 5: return
    body.ops.push(pack(OpCode::Return));
    // 6: end (block 1)
    body.ops.push(pack_imm_u(OpCode::End, 1));
    // 7: local.get 0
    body.ops.push(pack_imm_u(OpCode::LocalGet, 0));
    // 8: i32.const 1
    body.ops.push(pack_imm(OpCode::I32Const, 1));
    // 9: i32.sub
    body.ops.push(pack(OpCode::I32Sub));
    // 10: call fib (func 0)
    body.ops.push(pack_imm_u(OpCode::Call, 0));
    // 11: local.set 1
    body.ops.push(pack_imm_u(OpCode::LocalSet, 1));
    // 12: local.get 0
    body.ops.push(pack_imm_u(OpCode::LocalGet, 0));
    // 13: i32.const 2
    body.ops.push(pack_imm(OpCode::I32Const, 2));
    // 14: i32.sub
    body.ops.push(pack(OpCode::I32Sub));
    // 15: call fib (func 0)
    body.ops.push(pack_imm_u(OpCode::Call, 0));
    // 16: local.set 2
    body.ops.push(pack_imm_u(OpCode::LocalSet, 2));
    // 17: local.get 1
    body.ops.push(pack_imm_u(OpCode::LocalGet, 1));
    // 18: local.get 2
    body.ops.push(pack_imm_u(OpCode::LocalGet, 2));
    // 19: i32.add
    body.ops.push(pack(OpCode::I32Add));
    // 20: end (block 0 — function)
    body.ops.push(pack_imm_u(OpCode::End, 0));

    body.fuse();

    // Expected fused sequence (8 ops):
    // 0: LocalGetI32ConstLeSIf  0, 1, block1
    // 1: LocalGetReturn         0
    // 2: End(1)
    // 3: LocalGetI32ConstSub    0, 1
    // 4: CallLocalSet           0, 1
    // 5: LocalGetI32ConstSub    0, 2
    // 6: CallLocalSet           0, 2
    // 7: LocalGetLocalGetAdd    1, 2
    // 8: End(0)
    let opcodes: Vec<OpCode> = body.ops.iter().map(|op| op.opcode()).collect();
    assert_eq!(
        opcodes,
        vec![
            OpCode::LocalGetI32ConstLeSIf,
            OpCode::LocalGetReturn,
            OpCode::End,
            OpCode::LocalGetI32ConstSub,
            OpCode::CallLocalSet,
            OpCode::LocalGetI32ConstSub,
            OpCode::CallLocalSet,
            OpCode::LocalGetLocalGetAdd,
            OpCode::End,
        ]
    );
    assert_eq!(body.ops.len(), 9);

    // Verify block metadata was remapped correctly.
    // Function block: start=0, end=8 (the End(0) op).
    assert_eq!(body.blocks[0].start_pc, 0);
    assert_eq!(body.blocks[0].end_pc, 8);
    // If block: start=0 (fused into LocalGetI32ConstLeSIf), end=2 (End(1)).
    assert_eq!(body.blocks[1].start_pc, 0);
    assert_eq!(body.blocks[1].end_pc, 2);
}
