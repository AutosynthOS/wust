extern crate alloc;
use alloc::format;
use autosynth_isa::Instruction;

use crate::imm::{BImm13, JImm21, SImm12, SImm20};
use crate::inst::*;
use crate::reg::Gpr;

fn check_asm<I: Rv64Inst + Copy + core::fmt::Display>(inst: &I, expected: &str) {
    let mut buf = [0u8; 4];
    let wrapped = Rv64Instruction(*inst);
    let n = wrapped.encode(&mut buf).expect("encode failed");
    assert_eq!(n, 4);
    assert_eq!(format!("{inst}"), expected);
}

// ---- Add ----

#[test]
fn add_a0_a1() {
    let inst = Add { rd: Gpr::A0, rs1: Gpr::A0, rs2: Gpr::A1 };
    check_asm(&inst, "add a0, a0, a1");
}

#[test]
fn add_s0_s1_s2() {
    let inst = Add { rd: Gpr::S0, rs1: Gpr::S1, rs2: Gpr::S2 };
    check_asm(&inst, "add s0, s1, s2");
}

// ---- Addw ----

#[test]
fn addw_a0_a1_a2() {
    let inst = Addw { rd: Gpr::A0, rs1: Gpr::A1, rs2: Gpr::A2 };
    check_asm(&inst, "addw a0, a1, a2");
}

#[test]
fn addw_t0_t1_t2() {
    let inst = Addw { rd: Gpr::T0, rs1: Gpr::T1, rs2: Gpr::T2 };
    check_asm(&inst, "addw t0, t1, t2");
}

// ---- Sub ----

#[test]
fn sub_a0_a1_a2() {
    let inst = Sub { rd: Gpr::A0, rs1: Gpr::A1, rs2: Gpr::A2 };
    check_asm(&inst, "sub a0, a1, a2");
}

#[test]
fn sub_zero_t0_t1() {
    let inst = Sub { rd: Gpr::ZERO, rs1: Gpr::T0, rs2: Gpr::T1 };
    check_asm(&inst, "sub zero, t0, t1");
}

// ---- Subw ----

#[test]
fn subw_a0_a1_a2() {
    let inst = Subw { rd: Gpr::A0, rs1: Gpr::A1, rs2: Gpr::A2 };
    check_asm(&inst, "subw a0, a1, a2");
}

#[test]
fn subw_s0_s1_s2() {
    let inst = Subw { rd: Gpr::S0, rs1: Gpr::S1, rs2: Gpr::S2 };
    check_asm(&inst, "subw s0, s1, s2");
}

// ---- Addi ----

#[test]
fn addi_sp_minus_16() {
    let inst = Addi { rd: Gpr::SP, rs1: Gpr::SP, imm: SImm12::new(-16).unwrap() };
    check_asm(&inst, "addi sp, sp, -16");
}

#[test]
fn addi_a0_a1_42() {
    let inst = Addi { rd: Gpr::A0, rs1: Gpr::A1, imm: SImm12::new(42).unwrap() };
    check_asm(&inst, "addi a0, a1, 42");
}

#[test]
fn addi_nop() {
    let inst = Addi { rd: Gpr::ZERO, rs1: Gpr::ZERO, imm: SImm12::new(0).unwrap() };
    check_asm(&inst, "addi zero, zero, 0");
}

// ---- Addiw ----

#[test]
fn addiw_a0_a0_1() {
    let inst = Addiw { rd: Gpr::A0, rs1: Gpr::A0, imm: SImm12::new(1).unwrap() };
    check_asm(&inst, "addiw a0, a0, 1");
}

#[test]
fn addiw_s0_s0_neg5() {
    let inst = Addiw { rd: Gpr::S0, rs1: Gpr::S0, imm: SImm12::new(-5).unwrap() };
    check_asm(&inst, "addiw s0, s0, -5");
}

// ---- Or ----

#[test]
fn or_a0_a1_a2() {
    let inst = Or { rd: Gpr::A0, rs1: Gpr::A1, rs2: Gpr::A2 };
    check_asm(&inst, "or a0, a1, a2");
}

#[test]
fn or_t3_zero_t4() {
    let inst = Or { rd: Gpr::T3, rs1: Gpr::ZERO, rs2: Gpr::T4 };
    check_asm(&inst, "or t3, zero, t4");
}

// ---- Lui ----

#[test]
fn lui_a0_1() {
    let inst = Lui { rd: Gpr::A0, imm: SImm20::new(1).unwrap() };
    check_asm(&inst, "lui a0, 1");
}

#[test]
fn lui_t0_neg1() {
    let inst = Lui { rd: Gpr::T0, imm: SImm20::new(-1).unwrap() };
    check_asm(&inst, "lui t0, -1");
}

// ---- Lw ----

#[test]
fn lw_a0_0_sp() {
    let inst = Lw { rd: Gpr::A0, rs1: Gpr::SP, imm: SImm12::new(0).unwrap() };
    check_asm(&inst, "lw a0, 0(sp)");
}

#[test]
fn lw_s0_8_s1() {
    let inst = Lw { rd: Gpr::S0, rs1: Gpr::S1, imm: SImm12::new(8).unwrap() };
    check_asm(&inst, "lw s0, 8(s1)");
}

// ---- Ld ----

#[test]
fn ld_a0_0_sp() {
    let inst = Ld { rd: Gpr::A0, rs1: Gpr::SP, imm: SImm12::new(0).unwrap() };
    check_asm(&inst, "ld a0, 0(sp)");
}

#[test]
fn ld_ra_16_sp() {
    let inst = Ld { rd: Gpr::RA, rs1: Gpr::SP, imm: SImm12::new(16).unwrap() };
    check_asm(&inst, "ld ra, 16(sp)");
}

// ---- Sw ----

#[test]
fn sw_a0_0_sp() {
    let inst = Sw { rs2: Gpr::A0, rs1: Gpr::SP, imm: SImm12::new(0).unwrap() };
    check_asm(&inst, "sw a0, 0(sp)");
}

#[test]
fn sw_t0_neg4_s0() {
    let inst = Sw { rs2: Gpr::T0, rs1: Gpr::S0, imm: SImm12::new(-4).unwrap() };
    check_asm(&inst, "sw t0, -4(s0)");
}

// ---- Sd ----

#[test]
fn sd_ra_8_sp() {
    let inst = Sd { rs2: Gpr::RA, rs1: Gpr::SP, imm: SImm12::new(8).unwrap() };
    check_asm(&inst, "sd ra, 8(sp)");
}

#[test]
fn sd_s0_0_sp() {
    let inst = Sd { rs2: Gpr::S0, rs1: Gpr::SP, imm: SImm12::new(0).unwrap() };
    check_asm(&inst, "sd s0, 0(sp)");
}

// ---- Beq ----

#[test]
fn beq_a0_zero_16() {
    let inst = Beq { rs1: Gpr::A0, rs2: Gpr::ZERO, imm: BImm13::new(16).unwrap() };
    check_asm(&inst, "beq a0, zero, 16");
}

#[test]
fn beq_t0_t1_neg8() {
    let inst = Beq { rs1: Gpr::T0, rs2: Gpr::T1, imm: BImm13::new(-8).unwrap() };
    check_asm(&inst, "beq t0, t1, -8");
}

// ---- Bne ----

#[test]
fn bne_a0_a1_32() {
    let inst = Bne { rs1: Gpr::A0, rs2: Gpr::A1, imm: BImm13::new(32).unwrap() };
    check_asm(&inst, "bne a0, a1, 32");
}

#[test]
fn bne_s0_zero_neg16() {
    let inst = Bne { rs1: Gpr::S0, rs2: Gpr::ZERO, imm: BImm13::new(-16).unwrap() };
    check_asm(&inst, "bne s0, zero, -16");
}

// ---- Blt ----

#[test]
fn blt_a0_a1_64() {
    let inst = Blt { rs1: Gpr::A0, rs2: Gpr::A1, imm: BImm13::new(64).unwrap() };
    check_asm(&inst, "blt a0, a1, 64");
}

#[test]
fn blt_t0_t1_neg24() {
    let inst = Blt { rs1: Gpr::T0, rs2: Gpr::T1, imm: BImm13::new(-24).unwrap() };
    check_asm(&inst, "blt t0, t1, -24");
}

// ---- Bge ----

#[test]
fn bge_a0_a1_128() {
    let inst = Bge { rs1: Gpr::A0, rs2: Gpr::A1, imm: BImm13::new(128).unwrap() };
    check_asm(&inst, "bge a0, a1, 128");
}

#[test]
fn bge_s0_s1_neg4() {
    let inst = Bge { rs1: Gpr::S0, rs2: Gpr::S1, imm: BImm13::new(-4).unwrap() };
    check_asm(&inst, "bge s0, s1, -4");
}

// ---- Jal ----

#[test]
fn jal_ra_100() {
    let inst = Jal { rd: Gpr::RA, imm: JImm21::new(100).unwrap() };
    check_asm(&inst, "jal ra, 100");
}

#[test]
fn jal_zero_neg200() {
    let inst = Jal { rd: Gpr::ZERO, imm: JImm21::new(-200).unwrap() };
    check_asm(&inst, "jal zero, -200");
}

// ---- Jalr ----

#[test]
fn jalr_ret() {
    let inst = Jalr { rd: Gpr::ZERO, rs1: Gpr::RA, imm: SImm12::new(0).unwrap() };
    check_asm(&inst, "jalr zero, ra, 0");
}

#[test]
fn jalr_ra_t0_4() {
    let inst = Jalr { rd: Gpr::RA, rs1: Gpr::T0, imm: SImm12::new(4).unwrap() };
    check_asm(&inst, "jalr ra, t0, 4");
}

// ---- Immediate validation ----

#[test]
fn simm12_range() {
    assert!(SImm12::new(-2049).is_err());
    assert!(SImm12::new(2048).is_err());
    assert!(SImm12::new(-2048).is_ok());
    assert!(SImm12::new(2047).is_ok());
    assert!(SImm12::new(0).is_ok());
}

#[test]
fn simm20_range() {
    assert!(SImm20::new(-(1 << 19) - 1).is_err());
    assert!(SImm20::new(1 << 19).is_err());
    assert!(SImm20::new(-(1 << 19)).is_ok());
    assert!(SImm20::new((1 << 19) - 1).is_ok());
}

#[test]
fn bimm13_range_and_alignment() {
    assert!(BImm13::new(-4097).is_err());
    assert!(BImm13::new(4096).is_err());
    assert!(BImm13::new(3).is_err()); // odd = not aligned
    assert!(BImm13::new(-4096).is_ok());
    assert!(BImm13::new(4094).is_ok());
    assert!(BImm13::new(0).is_ok());
}

#[test]
fn jimm21_range_and_alignment() {
    assert!(JImm21::new(-(1 << 20) - 1).is_err());
    assert!(JImm21::new(1 << 20).is_err());
    assert!(JImm21::new(5).is_err()); // odd = not aligned
    assert!(JImm21::new(-(1 << 20)).is_ok());
    assert!(JImm21::new((1 << 20) - 2).is_ok());
    assert!(JImm21::new(0).is_ok());
}

// ---- Encoding correctness (spot-check against known-good values) ----

#[test]
fn add_encoding() {
    // ADD a0, a1, a2: R-type, funct7=0, rs2=a2(12), rs1=a1(11), funct3=0, rd=a0(10), opcode=0x33
    let inst = Add { rd: Gpr::A0, rs1: Gpr::A1, rs2: Gpr::A2 };
    let word = inst.encode_word();
    // 0000000 01100 01011 000 01010 0110011
    assert_eq!(word, 0x00C58533);
}

#[test]
fn sub_encoding() {
    // SUB a0, a1, a2: funct7=0x20, rs2=12, rs1=11, funct3=0, rd=10, opcode=0x33
    let inst = Sub { rd: Gpr::A0, rs1: Gpr::A1, rs2: Gpr::A2 };
    let word = inst.encode_word();
    // 0100000 01100 01011 000 01010 0110011
    assert_eq!(word, 0x40C58533);
}

#[test]
fn addi_encoding() {
    // ADDI sp, sp, -16: imm=0xFF0, rs1=sp(2), funct3=0, rd=sp(2), opcode=0x13
    let inst = Addi { rd: Gpr::SP, rs1: Gpr::SP, imm: SImm12::new(-16).unwrap() };
    let word = inst.encode_word();
    // 111111110000 00010 000 00010 0010011
    assert_eq!(word, 0xFF010113);
}

#[test]
fn sd_encoding() {
    // SD ra, 8(sp): imm=8, rs2=ra(1), rs1=sp(2), funct3=3
    // imm[11:5]=0, imm[4:0]=8
    // S-type: 0000000 00001 00010 011 01000 0100011
    let inst = Sd { rs2: Gpr::RA, rs1: Gpr::SP, imm: SImm12::new(8).unwrap() };
    let word = inst.encode_word();
    assert_eq!(word, 0x00113423);
}

#[test]
fn beq_encoding() {
    // BEQ a0, zero, 16: rs1=a0(10), rs2=zero(0), imm=16
    // imm bits: 12=0, 11=0, 10:5=000000, 4:1=1000
    // B-type: 0|000000 00000 01010 000 1000|0 1100011
    let inst = Beq { rs1: Gpr::A0, rs2: Gpr::ZERO, imm: BImm13::new(16).unwrap() };
    let word = inst.encode_word();
    assert_eq!(word, 0x00050863);
}

#[test]
fn jal_encoding() {
    // JAL ra, 100: rd=ra(1), imm=100 (0x64)
    // imm=100=0b0_0000000000_0_00000110_0100
    // J-type bits: imm[20]=0, imm[10:1]=0000110010, imm[11]=0, imm[19:12]=00000000
    // 0 0000110010 0 00000000 00001 1101111
    let inst = Jal { rd: Gpr::RA, imm: JImm21::new(100).unwrap() };
    let word = inst.encode_word();
    assert_eq!(word, 0x064000EF);
}

#[test]
fn jalr_encoding() {
    // JALR zero, ra, 0: rd=zero(0), rs1=ra(1), imm=0
    // I-type: 000000000000 00001 000 00000 1100111
    let inst = Jalr { rd: Gpr::ZERO, rs1: Gpr::RA, imm: SImm12::new(0).unwrap() };
    let word = inst.encode_word();
    assert_eq!(word, 0x00008067);
}

#[test]
fn lui_encoding() {
    // LUI a0, 1: rd=a0(10), imm=1
    // U-type: 00000000000000000001 01010 0110111
    let inst = Lui { rd: Gpr::A0, imm: SImm20::new(1).unwrap() };
    let word = inst.encode_word();
    assert_eq!(word, 0x00001537);
}

#[test]
fn lw_encoding() {
    // LW a0, 0(sp): imm=0, rs1=sp(2), funct3=2, rd=a0(10), opcode=0x03
    // I-type: 000000000000 00010 010 01010 0000011
    let inst = Lw { rd: Gpr::A0, rs1: Gpr::SP, imm: SImm12::new(0).unwrap() };
    let word = inst.encode_word();
    assert_eq!(word, 0x00012503);
}

#[test]
fn ld_encoding() {
    // LD ra, 16(sp): imm=16, rs1=sp(2), funct3=3, rd=ra(1), opcode=0x03
    // I-type: 000000010000 00010 011 00001 0000011
    let inst = Ld { rd: Gpr::RA, rs1: Gpr::SP, imm: SImm12::new(16).unwrap() };
    let word = inst.encode_word();
    assert_eq!(word, 0x01013083);
}

#[test]
fn or_encoding() {
    // OR a0, a1, a2: funct7=0, rs2=12, rs1=11, funct3=6, rd=10, opcode=0x33
    // 0000000 01100 01011 110 01010 0110011
    let inst = Or { rd: Gpr::A0, rs1: Gpr::A1, rs2: Gpr::A2 };
    let word = inst.encode_word();
    assert_eq!(word, 0x00C5E533);
}

#[test]
fn sw_encoding() {
    // SW a0, 0(sp): imm=0, rs2=a0(10), rs1=sp(2), funct3=2
    // S-type: 0000000 01010 00010 010 00000 0100011
    let inst = Sw { rs2: Gpr::A0, rs1: Gpr::SP, imm: SImm12::new(0).unwrap() };
    let word = inst.encode_word();
    assert_eq!(word, 0x00A12023);
}

// ---- Encode buffer too small ----

#[test]
fn encode_buffer_too_small() {
    let inst = Rv64Instruction(Add { rd: Gpr::A0, rs1: Gpr::A0, rs2: Gpr::A1 });
    let mut buf = [0u8; 3];
    assert!(inst.encode(&mut buf).is_err());
}
