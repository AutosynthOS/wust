use crate::jit::emit::{Cond, Emitter, Reg};

#[test]
fn encode_ret() {
    let mut e = Emitter::new();
    e.ret();
    assert_eq!(e.code()[0], 0xD65F03C0);
}

#[test]
fn encode_add_w() {
    let mut e: Emitter = Emitter::new();
    // ADD W0, W1, W2
    e.add_w(Reg::W0, Reg::W1, Reg::W2);
    // Expected: 0x0B020020
    assert_eq!(e.code()[0], 0x0B020020);
}

#[test]
fn encode_sub_w_imm() {
    let mut e = Emitter::new();
    // SUB W0, W1, #1
    e.sub_w_imm(Reg::W0, Reg::W1, 1);
    // Expected: 0x51000420
    assert_eq!(e.code()[0], 0x51000420);
}

#[test]
fn encode_subs_x_imm() {
    let mut e = Emitter::new();
    // SUBS X24, X24, #1
    // SUBS X24, X24, #1
    e.subs_x_imm(Reg(24), Reg(24), 1);
    // Expected: 0xF1000718
    assert_eq!(e.code()[0], 0xF1000718);
}

#[test]
fn encode_cmp_w_imm() {
    let mut e = Emitter::new();
    // CMP W9, #1  (SUBS WZR, W9, #1)
    e.cmp_w_imm(Reg::W9, 1);
    // Expected: 0x7100053F
    assert_eq!(e.code()[0], 0x7100053F);
}

#[test]
fn encode_movz_w() {
    let mut e = Emitter::new();
    // MOVZ W0, #42
    e.movz_w(Reg::W0, 42);
    // Expected: 0x52800540
    assert_eq!(e.code()[0], 0x52800540);
}

#[test]
fn encode_mov_w() {
    let mut e = Emitter::new();
    // MOV W0, W1 → ORR W0, WZR, W1
    e.mov_w(Reg::W0, Reg::W1);
    // Expected: 0x2A0103E0
    assert_eq!(e.code()[0], 0x2A0103E0);
}

#[test]
fn encode_stp_x_pre() {
    let mut e = Emitter::new();
    // STP X29, X30, [SP, #-16]!
    e.stp_x_pre(Reg::X29, Reg::X30, Reg::SP, -16);
    // Expected: 0xA9BF7BFD
    assert_eq!(e.code()[0], 0xA9BF7BFD);
}

#[test]
fn encode_ldp_x_post() {
    let mut e = Emitter::new();
    // LDP X29, X30, [SP], #16
    e.ldp_x_post(Reg::X29, Reg::X30, Reg::SP, 16);
    // Expected: 0xA8C17BFD
    assert_eq!(e.code()[0], 0xA8C17BFD);
}

#[test]
fn encode_str_x_uoff() {
    let mut e = Emitter::new();
    // STR X9, [X28, #0]
    e.str_x_uoff(Reg::X9, Reg(28), 0);
    // Expected: 0xF9000389
    assert_eq!(e.code()[0], 0xF9000389);
}

#[test]
fn encode_ldr_x_uoff() {
    let mut e = Emitter::new();
    // LDR X9, [X28, #8]
    e.ldr_x_uoff(Reg::X9, Reg(28), 8);
    // Expected: 0xF9400789
    assert_eq!(e.code()[0], 0xF9400789);
}

#[test]
fn encode_str_x_pre() {
    let mut e = Emitter::new();
    // STR X28, [SP, #-16]!
    e.str_x_pre(Reg(28), Reg::SP, -16);
    // Expected: 0xF81F0FFC
    assert_eq!(e.code()[0], 0xF81F0FFC);
}

#[test]
fn encode_ldr_x_post() {
    let mut e = Emitter::new();
    // LDR X28, [SP], #16
    e.ldr_x_post(Reg(28), Reg::SP, 16);
    // Expected: 0xF84107FC
    assert_eq!(e.code()[0], 0xF84107FC);
}

#[test]
fn encode_blr() {
    let mut e = Emitter::new();
    // BLR X9
    e.blr(Reg::X9);
    // Expected: 0xD63F0120
    assert_eq!(e.code()[0], 0xD63F0120);
}

#[test]
fn encode_cset_le() {
    let mut e = Emitter::new();
    // CSET W9, LE → CSINC W9, WZR, WZR, GT
    e.cset_w(Reg::W9, Cond::LE);
    // GT = 0b1100, CSINC: 0x1A800400 | (31 << 16) | (0xC << 12) | (31 << 5) | 9
    // = 0x1A9FC7E9
    // Wait, let me compute: 0x1A800400 = 0x1A800400
    // | (31 << 16) = 0x001F0000 → 0x1A9F0400
    // | (0xC << 12) = 0x0000C000 → 0x1A9FC400
    // | (31 << 5) = 0x000003E0 → 0x1A9FC7E0
    // | 9 → 0x1A9FC7E9
    assert_eq!(e.code()[0], 0x1A9FC7E9);
}

#[test]
fn patch_b_cond_forward() {
    let mut e = Emitter::new();
    let pp = e.b_cond(Cond::LE); // offset 0
    e.ret(); // offset 1
    e.ret(); // offset 2
    e.patch(pp); // target = offset 3
    // B.LE should branch +3 words from offset 0.
    // 0x54000000 | (3 << 5) | 0xD (LE)
    assert_eq!(e.code()[0], 0x5400006D);
}

#[test]
fn patch_cbz_forward() {
    let mut e = Emitter::new();
    let pp = e.cbz_w(Reg::W9); // offset 0
    e.ret(); // offset 1
    e.patch(pp); // target = offset 2
    // CBZ W9 +2 words: 0x34000000 | (2 << 5) | 9
    assert_eq!(e.code()[0], 0x34000049);
}

#[test]
fn encode_and_execute_add() {
    use crate::jit::code_buffer::CodeBuffer;

    let mut e = Emitter::new();
    // fn(a: i32, b: i32) -> i32 { a + b }
    // W0 = a, W1 = b on entry (C ABI)
    e.add_w(Reg::W0, Reg::W0, Reg::W1);
    e.ret();

    let mut buf = CodeBuffer::new(4096).unwrap();
    for &word in e.code() {
        buf.emit_u32(word);
    }
    buf.finalize().unwrap();

    let func: unsafe extern "C" fn(i32, i32) -> i32 = unsafe { std::mem::transmute(buf.entry()) };
    assert_eq!(unsafe { func(3, 5) }, 8);
    assert_eq!(unsafe { func(-1, 1) }, 0);
    assert_eq!(unsafe { func(100, 200) }, 300);
}

#[test]
fn encode_and_execute_branch() {
    use crate::jit::code_buffer::CodeBuffer;

    let mut e = Emitter::new();
    // fn(n: i32) -> i32 { if n <= 1 { return 42; } else { return 99; } }
    e.cmp_w_imm(Reg::W0, 1);
    let pp = e.b_cond(Cond::LE); // branch to base case
    e.movz_w(Reg::W0, 99); // else: return 99
    e.ret();
    e.patch(pp); // base case lands here
    e.movz_w(Reg::W0, 42); // return 42
    e.ret();

    let mut buf = CodeBuffer::new(4096).unwrap();
    for &word in e.code() {
        buf.emit_u32(word);
    }
    buf.finalize().unwrap();

    let func: unsafe extern "C" fn(i32) -> i32 = unsafe { std::mem::transmute(buf.entry()) };
    assert_eq!(unsafe { func(0) }, 42);
    assert_eq!(unsafe { func(1) }, 42);
    assert_eq!(unsafe { func(2) }, 99);
    assert_eq!(unsafe { func(-5) }, 42);
}
