/// Encoding helpers for x86_64 instructions.
///
/// These functions produce the raw bytes that make up REX prefixes,
/// ModR/M bytes, SIB bytes, and displacement fields.

/// Build a REX prefix byte.
///
/// - `w`: 1 for 64-bit operand size
/// - `r`: extension of ModR/M reg field (1 if reg is r8-r15)
/// - `x`: extension of SIB index field
/// - `b`: extension of ModR/M r/m field or SIB base (1 if r/m is r8-r15)
pub const fn rex(w: bool, r: bool, x: bool, b: bool) -> u8 {
    0x40 | ((w as u8) << 3) | ((r as u8) << 2) | ((x as u8) << 1) | (b as u8)
}

/// Build a ModR/M byte.
///
/// - `mode`: 2-bit mod field (0b00, 0b01, 0b10, 0b11)
/// - `reg`: 3-bit reg/opcode field (low 3 bits of register index)
/// - `rm`: 3-bit r/m field (low 3 bits of register index)
pub const fn modrm(mode: u8, reg: u8, rm: u8) -> u8 {
    ((mode & 0x03) << 6) | ((reg & 0x07) << 3) | (rm & 0x07)
}

/// Build a SIB byte.
///
/// - `scale`: 2-bit scale (0=1, 1=2, 2=4, 3=8)
/// - `index`: 3-bit index register (4 = none)
/// - `base`: 3-bit base register
pub const fn sib(scale: u8, index: u8, base: u8) -> u8 {
    ((scale & 0x03) << 6) | ((index & 0x07) << 3) | (base & 0x07)
}

/// Whether a REX prefix is needed for the given parameters.
pub const fn need_rex(w: bool, reg_ext: bool, rm_ext: bool) -> bool {
    w || reg_ext || rm_ext
}

/// Emit a register-register ALU instruction.
///
/// Format: [REX?] opcode ModR/M(11, reg, rm)
///
/// Returns number of bytes written.
pub fn emit_reg_reg(buf: &mut [u8], opcode: u8, is_64: bool, reg_ext: bool, rm_ext: bool, reg_low3: u8, rm_low3: u8) -> usize {
    let mut i = 0;
    if need_rex(is_64, reg_ext, rm_ext) {
        buf[i] = rex(is_64, reg_ext, false, rm_ext);
        i += 1;
    }
    buf[i] = opcode;
    i += 1;
    buf[i] = modrm(0b11, reg_low3, rm_low3);
    i += 1;
    i
}

/// Emit an ALU r/m, imm8 instruction (opcode 0x83).
///
/// Format: [REX?] 0x83 ModR/M(11, /n, rm) imm8
///
/// Returns number of bytes written.
pub fn emit_alu_imm8(buf: &mut [u8], ext_opcode: u8, is_64: bool, rm_ext: bool, rm_low3: u8, imm: u8) -> usize {
    let mut i = 0;
    if need_rex(is_64, false, rm_ext) {
        buf[i] = rex(is_64, false, false, rm_ext);
        i += 1;
    }
    buf[i] = 0x83;
    i += 1;
    buf[i] = modrm(0b11, ext_opcode, rm_low3);
    i += 1;
    buf[i] = imm;
    i += 1;
    i
}

/// Emit an ALU r/m, imm32 instruction (opcode 0x81).
///
/// Format: [REX?] 0x81 ModR/M(11, /n, rm) imm32
///
/// Returns number of bytes written.
pub fn emit_alu_imm32(buf: &mut [u8], ext_opcode: u8, is_64: bool, rm_ext: bool, rm_low3: u8, imm: i32) -> usize {
    let mut i = 0;
    if need_rex(is_64, false, rm_ext) {
        buf[i] = rex(is_64, false, false, rm_ext);
        i += 1;
    }
    buf[i] = 0x81;
    i += 1;
    buf[i] = modrm(0b11, ext_opcode, rm_low3);
    i += 1;
    let bytes = imm.to_le_bytes();
    buf[i..i + 4].copy_from_slice(&bytes);
    i += 4;
    i
}

/// Emit a memory operand (ModR/M + optional SIB + displacement).
///
/// Handles the special cases:
/// - rsp/r12 as base requires a SIB byte
/// - rbp/r13 as base with no displacement requires mod=01 with disp8=0
///
/// Returns number of bytes written starting at `buf[start]`.
pub fn emit_mem(buf: &mut [u8], start: usize, reg_low3: u8, base_low3: u8, base_ext: bool, disp: i32) -> usize {
    let _ = base_ext; // Extension bit is handled by REX in the caller.
    let mut i = start;
    let need_sib = base_low3 == 4; // rsp/r12

    if disp == 0 && base_low3 != 5 {
        // mod=00, no displacement (but rbp/r13 would be RIP-relative, handled below)
        buf[i] = modrm(0b00, reg_low3, if need_sib { 0b100 } else { base_low3 });
        i += 1;
        if need_sib {
            buf[i] = sib(0, 0b100, base_low3); // scale=1, index=none, base=rsp/r12
            i += 1;
        }
    } else if disp >= -128 && disp <= 127 {
        // mod=01, disp8
        buf[i] = modrm(0b01, reg_low3, if need_sib { 0b100 } else { base_low3 });
        i += 1;
        if need_sib {
            buf[i] = sib(0, 0b100, base_low3);
            i += 1;
        }
        buf[i] = disp as u8;
        i += 1;
    } else {
        // mod=10, disp32
        buf[i] = modrm(0b10, reg_low3, if need_sib { 0b100 } else { base_low3 });
        i += 1;
        if need_sib {
            buf[i] = sib(0, 0b100, base_low3);
            i += 1;
        }
        let bytes = disp.to_le_bytes();
        buf[i..i + 4].copy_from_slice(&bytes);
        i += 4;
    }
    i - start
}
