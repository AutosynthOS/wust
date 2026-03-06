extern crate alloc;
use alloc::format;
use autosynth_isa::Instruction;

use crate::cond::Cond;
use crate::imm::Imm32;
use crate::inst::*;
use crate::reg::*;

fn check_asm<I: X86_64Inst + Copy + core::fmt::Display>(
    inst: &I,
    expected_display: &str,
    expected_bytes: &[u8],
) {
    let mut buf = [0u8; 15];
    let wrapped = X86_64Instruction(*inst);
    let n = wrapped.encode(&mut buf).expect("encode failed");
    assert_eq!(
        &buf[..n],
        expected_bytes,
        "encoding mismatch for: {}",
        expected_display
    );
    assert_eq!(format!("{inst}"), expected_display);
}

// ---- AddRegReg ----

#[test]
fn add_reg_reg_32() {
    // add eax, ecx => 01 C8
    let inst = AddRegReg {
        dst: Gpr32::RAX.into(),
        src: Gpr32::RCX.into(),
    };
    check_asm(&inst, "add eax, ecx", &[0x01, 0xC8]);
}

#[test]
fn add_reg_reg_64() {
    // add rax, rcx => REX.W(48) 01 C8
    let inst = AddRegReg {
        dst: Gpr64::RAX.into(),
        src: Gpr64::RCX.into(),
    };
    check_asm(&inst, "add rax, rcx", &[0x48, 0x01, 0xC8]);
}

#[test]
fn add_reg_reg_extended() {
    // add r8d, r9d => REX(45) 01 C8
    // REX: 0x40 | B(r8d dst, ext) | R(r9d src, ext) = 0x40 | 0x01 | 0x04 = 0x45
    let inst = AddRegReg {
        dst: Gpr32::R8.into(),
        src: Gpr32::R9.into(),
    };
    check_asm(&inst, "add r8d, r9d", &[0x45, 0x01, 0xC8]);
}

// ---- SubRegReg ----

#[test]
fn sub_reg_reg_32() {
    // sub eax, ecx => 29 C8
    let inst = SubRegReg {
        dst: Gpr32::RAX.into(),
        src: Gpr32::RCX.into(),
    };
    check_asm(&inst, "sub eax, ecx", &[0x29, 0xC8]);
}

#[test]
fn sub_reg_reg_64() {
    // sub rax, rcx => REX.W(48) 29 C8
    let inst = SubRegReg {
        dst: Gpr64::RAX.into(),
        src: Gpr64::RCX.into(),
    };
    check_asm(&inst, "sub rax, rcx", &[0x48, 0x29, 0xC8]);
}

// ---- SubRegImm ----

#[test]
fn sub_reg_imm8_32() {
    // sub eax, 1 => 83 E8 01
    let inst = SubRegImm {
        dst: Gpr32::RAX.into(),
        imm: Imm32::new(1),
    };
    check_asm(&inst, "sub eax, 1", &[0x83, 0xE8, 0x01]);
}

#[test]
fn sub_reg_imm8_64() {
    // sub rax, 1 => REX.W(48) 83 E8 01
    let inst = SubRegImm {
        dst: Gpr64::RAX.into(),
        imm: Imm32::new(1),
    };
    check_asm(&inst, "sub rax, 1", &[0x48, 0x83, 0xE8, 0x01]);
}

#[test]
fn sub_reg_imm32_32() {
    // sub eax, 1000 => 81 E8 E8 03 00 00
    let inst = SubRegImm {
        dst: Gpr32::RAX.into(),
        imm: Imm32::new(1000),
    };
    check_asm(&inst, "sub eax, 1000", &[0x81, 0xE8, 0xE8, 0x03, 0x00, 0x00]);
}

#[test]
fn sub_reg_imm8_extended() {
    // sub r8d, 1 => REX.B(41) 83 E8 01
    let inst = SubRegImm {
        dst: Gpr32::R8.into(),
        imm: Imm32::new(1),
    };
    check_asm(&inst, "sub r8d, 1", &[0x41, 0x83, 0xE8, 0x01]);
}

// ---- CmpRegImm ----

#[test]
fn cmp_reg_imm8_32() {
    // cmp eax, 1 => 83 F8 01
    let inst = CmpRegImm {
        dst: Gpr32::RAX.into(),
        imm: Imm32::new(1),
    };
    check_asm(&inst, "cmp eax, 1", &[0x83, 0xF8, 0x01]);
}

#[test]
fn cmp_reg_imm8_64() {
    // cmp rax, 1 => REX.W(48) 83 F8 01
    let inst = CmpRegImm {
        dst: Gpr64::RAX.into(),
        imm: Imm32::new(1),
    };
    check_asm(&inst, "cmp rax, 1", &[0x48, 0x83, 0xF8, 0x01]);
}

#[test]
fn cmp_reg_imm32_32() {
    // cmp ecx, 1000 => 81 F9 E8 03 00 00
    let inst = CmpRegImm {
        dst: Gpr32::RCX.into(),
        imm: Imm32::new(1000),
    };
    check_asm(
        &inst,
        "cmp ecx, 1000",
        &[0x81, 0xF9, 0xE8, 0x03, 0x00, 0x00],
    );
}

// ---- MovRegReg ----

#[test]
fn mov_reg_reg_32() {
    // mov eax, ecx => 89 C8
    let inst = MovRegReg {
        dst: Gpr32::RAX.into(),
        src: Gpr32::RCX.into(),
    };
    check_asm(&inst, "mov eax, ecx", &[0x89, 0xC8]);
}

#[test]
fn mov_reg_reg_64() {
    // mov rax, rcx => REX.W(48) 89 C8
    let inst = MovRegReg {
        dst: Gpr64::RAX.into(),
        src: Gpr64::RCX.into(),
    };
    check_asm(&inst, "mov rax, rcx", &[0x48, 0x89, 0xC8]);
}

#[test]
fn mov_reg_reg_extended_src() {
    // mov eax, r8d => REX.R(44) 89 C0
    let inst = MovRegReg {
        dst: Gpr32::RAX.into(),
        src: Gpr32::R8.into(),
    };
    check_asm(&inst, "mov eax, r8d", &[0x44, 0x89, 0xC0]);
}

#[test]
fn mov_reg_reg_extended_dst() {
    // mov r8d, eax => REX.B(41) 89 C0
    let inst = MovRegReg {
        dst: Gpr32::R8.into(),
        src: Gpr32::RAX.into(),
    };
    check_asm(&inst, "mov r8d, eax", &[0x41, 0x89, 0xC0]);
}

// ---- MovRegImm ----

#[test]
fn mov_reg_imm_32() {
    // mov eax, 42 => B8 2A 00 00 00
    let inst = MovRegImm {
        dst: Gpr32::RAX.into(),
        imm: 42,
    };
    check_asm(
        &inst,
        "mov eax, 42",
        &[0xB8, 0x2A, 0x00, 0x00, 0x00],
    );
}

#[test]
fn mov_reg_imm_32_extended() {
    // mov r8d, 42 => REX.B(41) B8 2A 00 00 00
    let inst = MovRegImm {
        dst: Gpr32::R8.into(),
        imm: 42,
    };
    check_asm(
        &inst,
        "mov r8d, 42",
        &[0x41, 0xB8, 0x2A, 0x00, 0x00, 0x00],
    );
}

#[test]
fn mov_reg_imm_64_small() {
    // mov rax, 42 => REX.W(48) C7 C0 2A 00 00 00
    let inst = MovRegImm {
        dst: Gpr64::RAX.into(),
        imm: 42,
    };
    check_asm(
        &inst,
        "mov rax, 42",
        &[0x48, 0xC7, 0xC0, 0x2A, 0x00, 0x00, 0x00],
    );
}

#[test]
fn mov_reg_imm_64_large() {
    // mov rax, 0x1234567890ABCDEF => REX.W(48) B8 EF CD AB 90 78 56 34 12
    let inst = MovRegImm {
        dst: Gpr64::RAX.into(),
        imm: 0x1234567890ABCDEF_i64,
    };
    check_asm(
        &inst,
        "mov rax, 1311768467294899695",
        &[0x48, 0xB8, 0xEF, 0xCD, 0xAB, 0x90, 0x78, 0x56, 0x34, 0x12],
    );
}

#[test]
fn mov_reg_imm_64_negative() {
    // mov rax, -1 => REX.W(48) C7 C0 FF FF FF FF
    let inst = MovRegImm {
        dst: Gpr64::RAX.into(),
        imm: -1,
    };
    check_asm(
        &inst,
        "mov rax, -1",
        &[0x48, 0xC7, 0xC0, 0xFF, 0xFF, 0xFF, 0xFF],
    );
}

// ---- Push ----

#[test]
fn push_rbp() {
    // push rbp => 55
    let inst = Push { src: Gpr64::RBP };
    check_asm(&inst, "push rbp", &[0x55]);
}

#[test]
fn push_r12() {
    // push r12 => REX.B(41) 54
    let inst = Push { src: Gpr64::R12 };
    check_asm(&inst, "push r12", &[0x41, 0x54]);
}

// ---- Pop ----

#[test]
fn pop_rbp() {
    // pop rbp => 5D
    let inst = Pop { dst: Gpr64::RBP };
    check_asm(&inst, "pop rbp", &[0x5D]);
}

#[test]
fn pop_r12() {
    // pop r12 => REX.B(41) 5C
    let inst = Pop { dst: Gpr64::R12 };
    check_asm(&inst, "pop r12", &[0x41, 0x5C]);
}

// ---- Ret ----

#[test]
fn ret_simple() {
    let inst = Ret;
    check_asm(&inst, "ret", &[0xC3]);
}

// ---- CallRel32 ----

#[test]
fn call_rel32_positive() {
    // call +100 => E8 64 00 00 00
    let inst = CallRel32 { offset: 100 };
    check_asm(&inst, "call 100", &[0xE8, 0x64, 0x00, 0x00, 0x00]);
}

#[test]
fn call_rel32_negative() {
    // call -42 => E8 D6 FF FF FF
    let inst = CallRel32 { offset: -42 };
    check_asm(&inst, "call -42", &[0xE8, 0xD6, 0xFF, 0xFF, 0xFF]);
}

// ---- Jcc ----

#[test]
fn jcc_le() {
    // jle 100 => 0F 8E 64 00 00 00
    let inst = Jcc {
        cond: Cond::LE,
        offset: 100,
    };
    check_asm(&inst, "jle 100", &[0x0F, 0x8E, 0x64, 0x00, 0x00, 0x00]);
}

#[test]
fn jcc_ne_negative() {
    // jne -20 => 0F 85 EC FF FF FF
    let inst = Jcc {
        cond: Cond::NE,
        offset: -20,
    };
    check_asm(&inst, "jne -20", &[0x0F, 0x85, 0xEC, 0xFF, 0xFF, 0xFF]);
}

#[test]
fn jcc_g() {
    // jg 0 => 0F 8F 00 00 00 00
    let inst = Jcc {
        cond: Cond::G,
        offset: 0,
    };
    check_asm(&inst, "jg 0", &[0x0F, 0x8F, 0x00, 0x00, 0x00, 0x00]);
}

// ---- MovLoad ----

#[test]
fn mov_load_32_rbp_disp8() {
    // mov eax, [rbp + 8] => 8B 45 08
    let inst = MovLoad {
        dst: Gpr32::RAX.into(),
        base: Gpr64::RBP,
        disp: 8,
    };
    check_asm(&inst, "mov eax, [rbp + 8]", &[0x8B, 0x45, 0x08]);
}

#[test]
fn mov_load_64_rbp_disp8() {
    // mov rax, [rbp + 8] => REX.W(48) 8B 45 08
    let inst = MovLoad {
        dst: Gpr64::RAX.into(),
        base: Gpr64::RBP,
        disp: 8,
    };
    check_asm(&inst, "mov rax, [rbp + 8]", &[0x48, 0x8B, 0x45, 0x08]);
}

#[test]
fn mov_load_rax_base_no_disp() {
    // mov ecx, [rax] => 8B 08
    let inst = MovLoad {
        dst: Gpr32::RCX.into(),
        base: Gpr64::RAX,
        disp: 0,
    };
    check_asm(&inst, "mov ecx, [rax]", &[0x8B, 0x08]);
}

#[test]
fn mov_load_rbp_base_no_disp() {
    // rbp with disp=0 needs mod=01 + disp8=0: mov ecx, [rbp] => 8B 4D 00
    let inst = MovLoad {
        dst: Gpr32::RCX.into(),
        base: Gpr64::RBP,
        disp: 0,
    };
    check_asm(&inst, "mov ecx, [rbp]", &[0x8B, 0x4D, 0x00]);
}

#[test]
fn mov_load_rsp_base_disp8() {
    // rsp as base needs SIB: mov ecx, [rsp + 16] => 8B 4C 24 10
    let inst = MovLoad {
        dst: Gpr32::RCX.into(),
        base: Gpr64::RSP,
        disp: 16,
    };
    check_asm(&inst, "mov ecx, [rsp + 16]", &[0x8B, 0x4C, 0x24, 0x10]);
}

#[test]
fn mov_load_rsp_base_no_disp() {
    // rsp with no disp needs SIB: mov ecx, [rsp] => 8B 0C 24
    let inst = MovLoad {
        dst: Gpr32::RCX.into(),
        base: Gpr64::RSP,
        disp: 0,
    };
    check_asm(&inst, "mov ecx, [rsp]", &[0x8B, 0x0C, 0x24]);
}

#[test]
fn mov_load_disp32() {
    // mov eax, [rbp + 256] => 8B 85 00 01 00 00
    let inst = MovLoad {
        dst: Gpr32::RAX.into(),
        base: Gpr64::RBP,
        disp: 256,
    };
    check_asm(
        &inst,
        "mov eax, [rbp + 256]",
        &[0x8B, 0x85, 0x00, 0x01, 0x00, 0x00],
    );
}

#[test]
fn mov_load_r13_base_no_disp() {
    // r13 is like rbp — needs mod=01 + disp8=0: mov eax, [r13] => REX.B(41) 8B 45 00
    let inst = MovLoad {
        dst: Gpr32::RAX.into(),
        base: Gpr64::R13,
        disp: 0,
    };
    check_asm(&inst, "mov eax, [r13]", &[0x41, 0x8B, 0x45, 0x00]);
}

#[test]
fn mov_load_r12_base_disp8() {
    // r12 is like rsp — needs SIB: mov eax, [r12 + 8] => REX.B(41) 8B 44 24 08
    let inst = MovLoad {
        dst: Gpr32::RAX.into(),
        base: Gpr64::R12,
        disp: 8,
    };
    check_asm(&inst, "mov eax, [r12 + 8]", &[0x41, 0x8B, 0x44, 0x24, 0x08]);
}

// ---- MovStore ----

#[test]
fn mov_store_32_rbp_disp8() {
    // mov [rbp + 8], eax => 89 45 08
    let inst = MovStore {
        base: Gpr64::RBP,
        disp: 8,
        src: Gpr32::RAX.into(),
    };
    check_asm(&inst, "mov [rbp + 8], eax", &[0x89, 0x45, 0x08]);
}

#[test]
fn mov_store_64_rbp_disp8() {
    // mov [rbp + 8], rax => REX.W(48) 89 45 08
    let inst = MovStore {
        base: Gpr64::RBP,
        disp: 8,
        src: Gpr64::RAX.into(),
    };
    check_asm(&inst, "mov [rbp + 8], rax", &[0x48, 0x89, 0x45, 0x08]);
}

#[test]
fn mov_store_rsp_base() {
    // rsp as base needs SIB: mov [rsp + 16], ecx => 89 4C 24 10
    let inst = MovStore {
        base: Gpr64::RSP,
        disp: 16,
        src: Gpr32::RCX.into(),
    };
    check_asm(&inst, "mov [rsp + 16], ecx", &[0x89, 0x4C, 0x24, 0x10]);
}

// ---- Immediate validation ----

#[test]
fn imm32_fits_imm8() {
    assert!(Imm32::new(127).fits_imm8());
    assert!(Imm32::new(-128).fits_imm8());
    assert!(!Imm32::new(128).fits_imm8());
    assert!(!Imm32::new(-129).fits_imm8());
}

// ---- Register display ----

#[test]
fn register_display_names() {
    assert_eq!(format!("{}", Gpr32::RAX), "eax");
    assert_eq!(format!("{}", Gpr32::RCX), "ecx");
    assert_eq!(format!("{}", Gpr32::R8), "r8d");
    assert_eq!(format!("{}", Gpr32::R15), "r15d");
    assert_eq!(format!("{}", Gpr64::RAX), "rax");
    assert_eq!(format!("{}", Gpr64::RCX), "rcx");
    assert_eq!(format!("{}", Gpr64::R8), "r8");
    assert_eq!(format!("{}", Gpr64::R15), "r15");
}

// ---- Condition code display ----

#[test]
fn cond_display() {
    assert_eq!(format!("{}", Cond::LE), "le");
    assert_eq!(format!("{}", Cond::NE), "ne");
    assert_eq!(format!("{}", Cond::G), "g");
    assert_eq!(format!("{}", Cond::E), "e");
}

#[test]
fn cond_invert() {
    assert_eq!(Cond::LE.invert(), Cond::G);
    assert_eq!(Cond::E.invert(), Cond::NE);
    assert_eq!(Cond::B.invert(), Cond::AE);
}
