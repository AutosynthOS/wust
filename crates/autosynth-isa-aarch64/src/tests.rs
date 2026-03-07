extern crate alloc;
use alloc::format;
use autosynth_isa::Instruction;

use crate::cond::Cond;
use crate::imm::{SImm9, UImm12, UImm16};
use crate::inst::*;
use crate::reg::*;

fn check_asm<I: Aarch64Inst + Copy + core::fmt::Display>(inst: &I, expected: &str) {
    let mut buf = [0u8; 4];
    let wrapped = InstAdapter(*inst);
    let n = wrapped.encode(&mut buf).expect("encode failed");
    assert_eq!(n, 4);
    assert_eq!(format!("{inst}"), expected);
}

// ---- AddImm ----

#[test]
fn add_imm_x64() {
    let inst = AddImm {
        rd: XGpr::R29.into(),
        rn: XGpr::R29.into(),
        imm: UImm12::new(24).unwrap(),
    };
    check_asm(&inst, "add x29, x29, #24");
}

#[test]
fn add_imm_w32_sp() {
    let inst = AddImm {
        rd: WGpr::R0.into(),
        rn: GprOrSp::Sp,
        imm: UImm12::new(16).unwrap(),
    };
    check_asm(&inst, "add w0, sp, #16");
}

// ---- SubReg ----

#[test]
fn sub_reg_w32() {
    let inst = SubReg {
        rd: WGpr::R9.into(),
        rn: WGpr::R9.into(),
        rm: WGpr::R10.into(),
    };
    check_asm(&inst, "sub w9, w9, w10");
}

#[test]
fn sub_reg_x64_with_zr() {
    let inst = SubReg {
        rd: GprOrZr::Xzr,
        rn: XGpr::R1.into(),
        rm: XGpr::R2.into(),
    };
    check_asm(&inst, "sub xzr, x1, x2");
}

// ---- Movz ----

#[test]
fn movz_w32() {
    let inst = Movz {
        rd: WGpr::R0.into(),
        imm: UImm16::new(42),
        hw: 0,
    };
    check_asm(&inst, "movz w0, #42");
}

#[test]
fn movz_x64_shifted() {
    let inst = Movz {
        rd: XGpr::R9.into(),
        imm: UImm16::new(0xABCD),
        hw: 1,
    };
    check_asm(&inst, "movz x9, #43981, lsl #16");
}

// ---- LdrUoff ----

#[test]
fn ldr_uoff_w32() {
    let inst = LdrUoff {
        rt: WGpr::R9.into(),
        rn: XGpr::R29.into(),
        offset: UImm12::new(2).unwrap(),
    };
    check_asm(&inst, "ldr w9, [x29, #8]");
}

#[test]
fn ldr_uoff_x64_from_sp() {
    let inst = LdrUoff {
        rt: XGpr::R0.into(),
        rn: GprOrSp::Sp,
        offset: UImm12::new(2).unwrap(),
    };
    check_asm(&inst, "ldr x0, [sp, #16]");
}

// ---- StrUoff ----

#[test]
fn str_uoff_w32() {
    let inst = StrUoff {
        rt: WGpr::R10.into(),
        rn: XGpr::R29.into(),
        offset: UImm12::new(1).unwrap(),
    };
    check_asm(&inst, "str w10, [x29, #4]");
}

// ---- BCond ----

#[test]
fn b_cond_le() {
    let inst = BCond { cond: Cond::LE, offset: 10 };
    check_asm(&inst, "b.le #40");
}

#[test]
fn b_cond_negative() {
    let inst = BCond { cond: Cond::NE, offset: -5 };
    check_asm(&inst, "b.ne #-20");
}

// ---- Bl ----

#[test]
fn bl_positive() {
    let inst = Bl { offset: 100 };
    check_asm(&inst, "bl #400");
}

#[test]
fn bl_negative() {
    let inst = Bl { offset: -42 };
    check_asm(&inst, "bl #-168");
}

// ---- Ret ----

#[test]
fn ret_default() {
    check_asm(&Ret::new(), "ret");
}

#[test]
fn ret_custom() {
    let inst = Ret { rn: XGpr::R15 };
    check_asm(&inst, "ret x15");
}

// ---- LdrPost ----

#[test]
fn ldr_post_x64() {
    let inst = LdrPost {
        rt: XGpr::R30.into(),
        rn: GprOrSp::Sp,
        imm: SImm9::new(16).unwrap(),
    };
    check_asm(&inst, "ldr x30, [sp], #16");
}

// ---- SubImm ----

#[test]
fn sub_imm_w32() {
    let inst = SubImm {
        rd: WGpr::R12.into(),
        rn: WGpr::R9.into(),
        imm: UImm12::new(1).unwrap(),
    };
    check_asm(&inst, "sub w12, w9, #1");
}

#[test]
fn sub_imm_x64() {
    let inst = SubImm {
        rd: XGpr::R29.into(),
        rn: XGpr::R29.into(),
        imm: UImm12::new(24).unwrap(),
    };
    check_asm(&inst, "sub x29, x29, #24");
}

// ---- SubsImm ----

#[test]
fn subs_imm_cmp_w32() {
    let inst = SubsImm {
        rd: GprOrZr::Wzr,
        rn: WGpr::R9.into(),
        imm: UImm12::new(1).unwrap(),
    };
    check_asm(&inst, "subs wzr, w9, #1");
}

#[test]
fn subs_imm_x64() {
    let inst = SubsImm {
        rd: GprOrZr::Xzr,
        rn: XGpr::R9.into(),
        imm: UImm12::new(1).unwrap(),
    };
    check_asm(&inst, "subs xzr, x9, #1");
}

// ---- AddReg ----

#[test]
fn add_reg_w32() {
    let inst = AddReg {
        rd: WGpr::R9.into(),
        rn: WGpr::R10.into(),
        rm: WGpr::R9.into(),
    };
    check_asm(&inst, "add w9, w10, w9");
}

#[test]
fn add_reg_x64() {
    let inst = AddReg {
        rd: XGpr::R0.into(),
        rn: XGpr::R1.into(),
        rm: XGpr::R2.into(),
    };
    check_asm(&inst, "add x0, x1, x2");
}

// ---- OrrReg ----

#[test]
fn orr_reg_mov_w32() {
    let inst = OrrReg {
        rd: WGpr::R9.into(),
        rn: GprOrZr::Wzr,
        rm: WGpr::R12.into(),
    };
    check_asm(&inst, "orr w9, wzr, w12");
}

#[test]
fn orr_reg_x64() {
    let inst = OrrReg {
        rd: XGpr::R0.into(),
        rn: GprOrZr::Xzr,
        rm: XGpr::R1.into(),
    };
    check_asm(&inst, "orr x0, xzr, x1");
}

// ---- StrPre ----

#[test]
fn str_pre_x64() {
    let inst = StrPre {
        rt: XGpr::R30.into(),
        rn: GprOrSp::Sp,
        imm: SImm9::new(-16).unwrap(),
    };
    check_asm(&inst, "str x30, [sp, #-16]!");
}

#[test]
fn str_pre_w32() {
    let inst = StrPre {
        rt: WGpr::R10.into(),
        rn: XGpr::R29.into(),
        imm: SImm9::new(-4).unwrap(),
    };
    check_asm(&inst, "str w10, [x29, #-4]!");
}

// ---- Immediate validation ----

#[test]
fn uimm12_range() {
    assert!(UImm12::new(4096).is_err());
    assert!(UImm12::new(4095).is_ok());
    assert!(UImm12::new(0).is_ok());
}

#[test]
fn simm9_range() {
    assert!(SImm9::new(-257).is_err());
    assert!(SImm9::new(256).is_err());
    assert!(SImm9::new(-256).is_ok());
    assert!(SImm9::new(255).is_ok());
}
