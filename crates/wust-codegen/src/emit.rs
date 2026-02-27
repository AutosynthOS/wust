/// Aarch64 register identifier (0–31).
///
/// Register 31 is context-dependent: it encodes ZR (zero register) in most
/// instructions, but SP (stack pointer) in base-address contexts
/// (load/store, add/sub immediate with SP).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct Reg(pub u8);

impl Reg {
    pub const W0: Reg = Reg(0);
    pub const W1: Reg = Reg(1);
    pub const W2: Reg = Reg(2);
    pub const W9: Reg = Reg(9);
    pub const X0: Reg = Reg(0);
    pub const X9: Reg = Reg(9);
    pub const X10: Reg = Reg(10);
    pub const X20: Reg = Reg(20);
    pub const X21: Reg = Reg(21);
    pub const X29: Reg = Reg(29);
    pub const X30: Reg = Reg(30);
    pub const XZR: Reg = Reg(31);
    pub const SP: Reg = Reg(31);
}

/// Condition codes for conditional branches.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Cond {
    EQ = 0b0000,
    NE = 0b0001,
    CS = 0b0010,
    CC = 0b0011,
    MI = 0b0100,
    PL = 0b0101,
    VS = 0b0110,
    VC = 0b0111,
    HI = 0b1000,
    LS = 0b1001,
    GE = 0b1010,
    LT = 0b1011,
    GT = 0b1100,
    LE = 0b1101,
    AL = 0b1110,
}

impl Cond {
    /// Invert the condition (e.g., LE → GT, EQ → NE).
    pub fn invert(self) -> Self {
        // On aarch64, inverting a condition flips bit 0.
        let bits = (self as u8) ^ 1;
        // Safety: all 4-bit values with bit 0 flipped produce valid Cond variants.
        unsafe { std::mem::transmute(bits) }
    }
}

/// A location in the instruction stream that needs to be patched with a
/// branch displacement once the target is known.
#[derive(Debug, Clone, Copy)]
pub struct PatchPoint {
    /// Index into the `code` vec (in u32 words).
    pub(crate) index: usize,
}

/// Low-level aarch64 instruction encoder.
///
/// Appends u32 instruction words to an internal buffer. The caller
/// (compiler.rs) decides *what* to emit; this struct only knows *how*
/// to encode each instruction form.
pub struct Emitter {
    pub(crate) code: Vec<u32>,
    /// Word offsets recorded by `mark()` — one per logical boundary.
    pub(crate) markers: Vec<usize>,
}

impl Emitter {
    pub fn new() -> Self {
        Emitter {
            code: Vec::with_capacity(256),
            markers: Vec::new(),
        }
    }

    /// Record the current word offset as a boundary marker.
    pub fn mark(&mut self) {
        self.markers.push(self.code.len());
    }

    /// Current offset in u32 words.
    pub fn offset(&self) -> usize {
        self.code.len()
    }

    /// Access the emitted instruction stream.
    pub fn code(&self) -> &[u32] {
        &self.code
    }

    /// Access the recorded boundary markers.
    pub fn markers(&self) -> &[usize] {
        &self.markers
    }

    // ---- Arithmetic (register) ----

    /// `ADD Wd, Wn, Wm` — 32-bit register add.
    pub fn add_w(&mut self, rd: Reg, rn: Reg, rm: Reg) {
        // sf=0, op=0, S=0, shift=00, Rm, imm6=0, Rn, Rd
        let inst = 0x0B000000
            | (rm.0 as u32 & 0x1F) << 16
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `SUB Wd, Wn, Wm` — 32-bit register sub.
    pub fn sub_w(&mut self, rd: Reg, rn: Reg, rm: Reg) {
        let inst = 0x4B000000
            | (rm.0 as u32 & 0x1F) << 16
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `ADD Xd, Xn, Xm` — 64-bit register add.
    pub fn add_x(&mut self, rd: Reg, rn: Reg, rm: Reg) {
        let inst = 0x8B000000
            | (rm.0 as u32 & 0x1F) << 16
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `SUB Xd, Xn, Xm` — 64-bit register sub.
    pub fn sub_x(&mut self, rd: Reg, rn: Reg, rm: Reg) {
        let inst = 0xCB000000
            | (rm.0 as u32 & 0x1F) << 16
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    // ---- Multiply ----

    /// `MUL Wd, Wn, Wm` — 32-bit multiply (alias: MADD Wd, Wn, Wm, WZR).
    pub fn mul_w(&mut self, rd: Reg, rn: Reg, rm: Reg) {
        let inst = 0x1B000000
            | (rm.0 as u32 & 0x1F) << 16
            | (31u32 << 10) // Ra = WZR
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `MUL Xd, Xn, Xm` — 64-bit multiply (alias: MADD Xd, Xn, Xm, XZR).
    pub fn mul_x(&mut self, rd: Reg, rn: Reg, rm: Reg) {
        let inst = 0x9B000000
            | (rm.0 as u32 & 0x1F) << 16
            | (31u32 << 10) // Ra = XZR
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    // ---- Division ----

    /// `SDIV Wd, Wn, Wm` — 32-bit signed divide.
    pub fn sdiv_w(&mut self, rd: Reg, rn: Reg, rm: Reg) {
        let inst = 0x1AC00C00
            | (rm.0 as u32 & 0x1F) << 16
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `UDIV Wd, Wn, Wm` — 32-bit unsigned divide.
    pub fn udiv_w(&mut self, rd: Reg, rn: Reg, rm: Reg) {
        let inst = 0x1AC00800
            | (rm.0 as u32 & 0x1F) << 16
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `SDIV Xd, Xn, Xm` — 64-bit signed divide.
    pub fn sdiv_x(&mut self, rd: Reg, rn: Reg, rm: Reg) {
        let inst = 0x9AC00C00
            | (rm.0 as u32 & 0x1F) << 16
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `UDIV Xd, Xn, Xm` — 64-bit unsigned divide.
    pub fn udiv_x(&mut self, rd: Reg, rn: Reg, rm: Reg) {
        let inst = 0x9AC00800
            | (rm.0 as u32 & 0x1F) << 16
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `MSUB Wd, Wn, Wm, Wa` — 32-bit multiply-subtract: Wa - Wn*Wm.
    pub fn msub_w(&mut self, rd: Reg, rn: Reg, rm: Reg, ra: Reg) {
        let inst = 0x1B008000
            | (rm.0 as u32 & 0x1F) << 16
            | (ra.0 as u32 & 0x1F) << 10
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `MSUB Xd, Xn, Xm, Xa` — 64-bit multiply-subtract: Xa - Xn*Xm.
    pub fn msub_x(&mut self, rd: Reg, rn: Reg, rm: Reg, ra: Reg) {
        let inst = 0x9B008000
            | (rm.0 as u32 & 0x1F) << 16
            | (ra.0 as u32 & 0x1F) << 10
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    // ---- Bitwise logic ----

    /// `AND Wd, Wn, Wm` — 32-bit bitwise AND.
    pub fn and_w(&mut self, rd: Reg, rn: Reg, rm: Reg) {
        let inst = 0x0A000000
            | (rm.0 as u32 & 0x1F) << 16
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `ORR Wd, Wn, Wm` — 32-bit bitwise OR.
    pub fn orr_w(&mut self, rd: Reg, rn: Reg, rm: Reg) {
        let inst = 0x2A000000
            | (rm.0 as u32 & 0x1F) << 16
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `EOR Wd, Wn, Wm` — 32-bit bitwise exclusive OR.
    pub fn eor_w(&mut self, rd: Reg, rn: Reg, rm: Reg) {
        let inst = 0x4A000000
            | (rm.0 as u32 & 0x1F) << 16
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `AND Xd, Xn, Xm` — 64-bit bitwise AND.
    pub fn and_x(&mut self, rd: Reg, rn: Reg, rm: Reg) {
        let inst = 0x8A000000
            | (rm.0 as u32 & 0x1F) << 16
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `ORR Xd, Xn, Xm` — 64-bit bitwise OR.
    pub fn orr_x(&mut self, rd: Reg, rn: Reg, rm: Reg) {
        let inst = 0xAA000000
            | (rm.0 as u32 & 0x1F) << 16
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `EOR Xd, Xn, Xm` — 64-bit bitwise exclusive OR.
    pub fn eor_x(&mut self, rd: Reg, rn: Reg, rm: Reg) {
        let inst = 0xCA000000
            | (rm.0 as u32 & 0x1F) << 16
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    // ---- Shifts ----

    /// `LSL Wd, Wn, Wm` — 32-bit logical shift left (alias: LSLV).
    pub fn lsl_w(&mut self, rd: Reg, rn: Reg, rm: Reg) {
        let inst = 0x1AC02000
            | (rm.0 as u32 & 0x1F) << 16
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `LSR Wd, Wn, Wm` — 32-bit logical shift right (alias: LSRV).
    pub fn lsr_w(&mut self, rd: Reg, rn: Reg, rm: Reg) {
        let inst = 0x1AC02400
            | (rm.0 as u32 & 0x1F) << 16
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `ASR Wd, Wn, Wm` — 32-bit arithmetic shift right (alias: ASRV).
    pub fn asr_w(&mut self, rd: Reg, rn: Reg, rm: Reg) {
        let inst = 0x1AC02800
            | (rm.0 as u32 & 0x1F) << 16
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `ROR Wd, Wn, Wm` — 32-bit rotate right (alias: RORV).
    pub fn ror_w(&mut self, rd: Reg, rn: Reg, rm: Reg) {
        let inst = 0x1AC02C00
            | (rm.0 as u32 & 0x1F) << 16
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `LSL Xd, Xn, Xm` — 64-bit logical shift left (alias: LSLV).
    pub fn lsl_x(&mut self, rd: Reg, rn: Reg, rm: Reg) {
        let inst = 0x9AC02000
            | (rm.0 as u32 & 0x1F) << 16
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `LSR Xd, Xn, Xm` — 64-bit logical shift right (alias: LSRV).
    pub fn lsr_x(&mut self, rd: Reg, rn: Reg, rm: Reg) {
        let inst = 0x9AC02400
            | (rm.0 as u32 & 0x1F) << 16
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `ASR Xd, Xn, Xm` — 64-bit arithmetic shift right (alias: ASRV).
    pub fn asr_x(&mut self, rd: Reg, rn: Reg, rm: Reg) {
        let inst = 0x9AC02800
            | (rm.0 as u32 & 0x1F) << 16
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `ROR Xd, Xn, Xm` — 64-bit rotate right (alias: RORV).
    pub fn ror_x(&mut self, rd: Reg, rn: Reg, rm: Reg) {
        let inst = 0x9AC02C00
            | (rm.0 as u32 & 0x1F) << 16
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    // ---- Bit manipulation ----

    /// `CLZ Wd, Wn` — 32-bit count leading zeros.
    pub fn clz_w(&mut self, rd: Reg, rn: Reg) {
        let inst = 0x5AC01000
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `CLZ Xd, Xn` — 64-bit count leading zeros.
    pub fn clz_x(&mut self, rd: Reg, rn: Reg) {
        let inst = 0xDAC01000
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `RBIT Wd, Wn` — 32-bit reverse bits.
    pub fn rbit_w(&mut self, rd: Reg, rn: Reg) {
        let inst = 0x5AC00000
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `RBIT Xd, Xn` — 64-bit reverse bits.
    pub fn rbit_x(&mut self, rd: Reg, rn: Reg) {
        let inst = 0xDAC00000
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    // ---- Arithmetic (immediate) ----

    /// `ADD Xd, Xn, #imm12` — 64-bit immediate add.
    pub fn add_x_imm(&mut self, rd: Reg, rn: Reg, imm: u16) {
        debug_assert!(imm < 4096);
        let inst = 0x91000000
            | (imm as u32 & 0xFFF) << 10
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `ADD Wd, Wn, #imm12` — 32-bit immediate add.
    pub fn add_w_imm(&mut self, rd: Reg, rn: Reg, imm: u16) {
        debug_assert!(imm < 4096);
        let inst = 0x11000000
            | (imm as u32 & 0xFFF) << 10
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `SUB Xd, Xn, #imm12` — 64-bit immediate sub.
    pub fn sub_x_imm(&mut self, rd: Reg, rn: Reg, imm: u16) {
        debug_assert!(imm < 4096);
        let inst = 0xD1000000
            | (imm as u32 & 0xFFF) << 10
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `SUB Wd, Wn, #imm12` — 32-bit immediate sub.
    pub fn sub_w_imm(&mut self, rd: Reg, rn: Reg, imm: u16) {
        debug_assert!(imm < 4096);
        let inst = 0x51000000
            | (imm as u32 & 0xFFF) << 10
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `SUBS Xd, Xn, #imm12` — 64-bit immediate sub, sets flags.
    pub fn subs_x_imm(&mut self, rd: Reg, rn: Reg, imm: u16) {
        debug_assert!(imm < 4096);
        let inst = 0xF1000000
            | (imm as u32 & 0xFFF) << 10
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `CMP Wn, #imm12` — alias for `SUBS WZR, Wn, #imm12`.
    pub fn cmp_w_imm(&mut self, rn: Reg, imm: u16) {
        debug_assert!(imm < 4096);
        // sf=0, op=1, S=1 → 0x71, Rd=WZR(31)
        let inst = 0x71000000 | (imm as u32 & 0xFFF) << 10 | (rn.0 as u32 & 0x1F) << 5 | 31; // Rd = WZR
        self.code.push(inst);
    }

    /// `CMP Xn, #imm12` — alias for `SUBS XZR, Xn, #imm12`.
    pub fn cmp_x_imm(&mut self, rn: Reg, imm: u16) {
        debug_assert!(imm < 4096);
        // sf=1, op=1, S=1 → 0xF1, Rd=XZR(31)
        let inst = 0xF1000000 | (imm as u32 & 0xFFF) << 10 | (rn.0 as u32 & 0x1F) << 5 | 31;
        self.code.push(inst);
    }

    /// `CMP Wn, Wm` — alias for `SUBS WZR, Wn, Wm`.
    pub fn cmp_w_reg(&mut self, rn: Reg, rm: Reg) {
        let inst = 0x6B000000 | ((rm.0 as u32) & 0x1F) << 16 | ((rn.0 as u32) & 0x1F) << 5 | 31; // Rd = WZR
        self.code.push(inst);
    }

    /// `CSET Wd, cond` — alias for `CSINC Wd, WZR, WZR, invert(cond)`.
    pub fn cset_w(&mut self, rd: Reg, cond: Cond) {
        // Invert the condition (flip bit 0).
        let inv_cond = (cond as u32) ^ 1;
        // CSINC Wd, WZR, WZR, inv_cond
        // sf=0, op=0, S=0, Rm=WZR(31), cond, o2=1, Rn=WZR(31), Rd
        let inst = 0x1A800400
            | (31u32 << 16) // Rm = WZR
            | (inv_cond << 12)
            | (31u32 << 5) // Rn = WZR
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `CMP Xn, Xm` — alias for `SUBS XZR, Xn, Xm`.
    pub fn cmp_x_reg(&mut self, rn: Reg, rm: Reg) {
        let inst = 0xEB000000
            | ((rm.0 as u32) & 0x1F) << 16
            | ((rn.0 as u32) & 0x1F) << 5
            | 31; // Rd = XZR
        self.code.push(inst);
    }

    /// `CSET Xd, cond` — alias for `CSINC Xd, XZR, XZR, invert(cond)`.
    pub fn cset_x(&mut self, rd: Reg, cond: Cond) {
        let inv_cond = (cond as u32) ^ 1;
        let inst = 0x9A800400
            | (31u32 << 16) // Rm = XZR
            | (inv_cond << 12)
            | (31u32 << 5) // Rn = XZR
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    // ---- Sign/zero extension ----

    /// `SXTW Xd, Wn` — sign-extend 32-bit to 64-bit (alias: SBFM Xd, Xn, #0, #31).
    pub fn sxtw(&mut self, rd: Reg, rn: Reg) {
        let inst = 0x93407C00
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `UXTW Xd, Wn` — zero-extend 32-bit to 64-bit (alias: MOV Wd, Wn which zeroes high 32 bits).
    /// Actually encoded as `MOV Wd, Wn` (ORR Wd, WZR, Wn) since writing Wd zeroes bits [63:32].
    pub fn uxtw(&mut self, rd: Reg, rn: Reg) {
        self.mov_w(rd, rn);
    }

    /// `SXTB Wd, Wn` — sign-extend byte to 32-bit (alias: SBFM Wd, Wn, #0, #7).
    pub fn sxtb_w(&mut self, rd: Reg, rn: Reg) {
        let inst = 0x13001C00
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `SXTH Wd, Wn` — sign-extend halfword to 32-bit (alias: SBFM Wd, Wn, #0, #15).
    pub fn sxth_w(&mut self, rd: Reg, rn: Reg) {
        let inst = 0x13003C00
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `SXTB Xd, Xn` — sign-extend byte to 64-bit (alias: SBFM Xd, Xn, #0, #7).
    pub fn sxtb_x(&mut self, rd: Reg, rn: Reg) {
        let inst = 0x93401C00
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `SXTH Xd, Xn` — sign-extend halfword to 64-bit (alias: SBFM Xd, Xn, #0, #15).
    pub fn sxth_x(&mut self, rd: Reg, rn: Reg) {
        let inst = 0x93403C00
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `SXTW Xd, Wn` — sign-extend word to 64-bit (alias: SBFM Xd, Xn, #0, #31).
    /// Same as sxtw, kept as alias for clarity.
    pub fn sxtw_x(&mut self, rd: Reg, rn: Reg) {
        self.sxtw(rd, rn);
    }

    // ---- Moves ----

    /// `MOV Wd, Wn` — alias for `ORR Wd, WZR, Wn`.
    pub fn mov_w(&mut self, rd: Reg, rn: Reg) {
        // ORR Wd, WZR, Wn (shifted register, shift=0, imm6=0)
        let inst = 0x2A000000
            | (rn.0 as u32 & 0x1F) << 16
            | (31u32 << 5) // Rn = WZR
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `MOV Xd, Xn` — alias for `ORR Xd, XZR, Xn`.
    pub fn mov_x(&mut self, rd: Reg, rn: Reg) {
        let inst = 0xAA000000
            | (rn.0 as u32 & 0x1F) << 16
            | (31u32 << 5) // Rn = XZR
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `MOV Xd, SP` — read the stack pointer into a general register.
    ///
    /// Encoded as `ADD Xd, SP, #0`. Needed because `MOV Xd, Xn` (ORR)
    /// can't access SP.
    pub fn mov_x_from_sp(&mut self, rd: Reg) {
        // ADD Xd, SP, #0  — Rn=31(SP) in ADD-imm context
        self.code.push(0x910003E0 | (rd.0 as u32 & 0x1F));
    }

    /// `MOV SP, Xn` — write a general register to the stack pointer.
    ///
    /// Encoded as `ADD SP, Xn, #0`.
    pub fn mov_sp_from(&mut self, rn: Reg) {
        // ADD SP, Xn, #0  — Rd=31(SP) in ADD-imm context
        self.code.push(0x9100001F | ((rn.0 as u32 & 0x1F) << 5));
    }

    /// `MOVZ Wd, #imm16` — move 16-bit immediate to register, zero rest.
    pub fn movz_w(&mut self, rd: Reg, imm: u16) {
        let inst = 0x52800000 | (imm as u32) << 5 | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `MOVN Wd, #imm16` — move inverted 16-bit immediate to register.
    pub fn movn_w(&mut self, rd: Reg, imm: u16) {
        let inst = 0x12800000 | (imm as u32) << 5 | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `MOVZ Xd, #imm16` — move 16-bit immediate to 64-bit register, zero rest.
    pub fn movz_x(&mut self, rd: Reg, imm: u16) {
        let inst = 0xD2800000 | (imm as u32) << 5 | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    // ---- Memory: store/load pair (pre-index / post-index) ----

    /// `STP Xt1, Xt2, [Xn, #imm]!` — store pair, pre-index, 64-bit.
    pub fn stp_x_pre(&mut self, rt1: Reg, rt2: Reg, rn: Reg, offset: i16) {
        debug_assert!(offset % 8 == 0, "STP offset must be 8-byte aligned");
        let imm7 = ((offset / 8) as u32) & 0x7F;
        let inst = 0xA9800000
            | imm7 << 15
            | (rt2.0 as u32 & 0x1F) << 10
            | (rn.0 as u32 & 0x1F) << 5
            | (rt1.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `LDP Xt1, Xt2, [Xn], #imm` — load pair, post-index, 64-bit.
    pub fn ldp_x_post(&mut self, rt1: Reg, rt2: Reg, rn: Reg, offset: i16) {
        debug_assert!(offset % 8 == 0, "LDP offset must be 8-byte aligned");
        let imm7 = ((offset / 8) as u32) & 0x7F;
        let inst = 0xA8C00000
            | imm7 << 15
            | (rt2.0 as u32 & 0x1F) << 10
            | (rn.0 as u32 & 0x1F) << 5
            | (rt1.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `STP Xt1, Xt2, [Xn, #imm]` — store pair, signed offset, 64-bit.
    pub fn stp_x_soff(&mut self, rt1: Reg, rt2: Reg, rn: Reg, offset: i16) {
        debug_assert!(offset % 8 == 0, "STP offset must be 8-byte aligned");
        let imm7 = ((offset / 8) as u32) & 0x7F;
        let inst = 0xA9000000
            | imm7 << 15
            | (rt2.0 as u32 & 0x1F) << 10
            | (rn.0 as u32 & 0x1F) << 5
            | (rt1.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `LDP Xt1, Xt2, [Xn, #imm]` — load pair, signed offset, 64-bit.
    pub fn ldp_x_soff(&mut self, rt1: Reg, rt2: Reg, rn: Reg, offset: i16) {
        debug_assert!(offset % 8 == 0, "LDP offset must be 8-byte aligned");
        let imm7 = ((offset / 8) as u32) & 0x7F;
        let inst = 0xA9400000
            | imm7 << 15
            | (rt2.0 as u32 & 0x1F) << 10
            | (rn.0 as u32 & 0x1F) << 5
            | (rt1.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    // ---- Memory: single register load/store ----

    /// `STR Xt, [Xn, #imm12*8]` — store 64-bit, unsigned offset.
    pub fn str_x_uoff(&mut self, rt: Reg, rn: Reg, offset: u16) {
        debug_assert!(offset % 8 == 0, "STR offset must be 8-byte aligned");
        let imm12 = (offset / 8) as u32;
        debug_assert!(imm12 < 4096);
        let inst = 0xF9000000 | imm12 << 10 | (rn.0 as u32 & 0x1F) << 5 | (rt.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `LDR Xt, [Xn, #imm12*8]` — load 64-bit, unsigned offset.
    pub fn ldr_x_uoff(&mut self, rt: Reg, rn: Reg, offset: u16) {
        debug_assert!(offset % 8 == 0, "LDR offset must be 8-byte aligned");
        let imm12 = (offset / 8) as u32;
        debug_assert!(imm12 < 4096);
        let inst = 0xF9400000 | imm12 << 10 | (rn.0 as u32 & 0x1F) << 5 | (rt.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `STR Xt, [Xn, #simm9]!` — store 64-bit, pre-index.
    pub fn str_x_pre(&mut self, rt: Reg, rn: Reg, offset: i16) {
        let imm9 = (offset as u32) & 0x1FF;
        let inst = 0xF8000C00 | imm9 << 12 | (rn.0 as u32 & 0x1F) << 5 | (rt.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `LDR Xt, [Xn], #simm9` — load 64-bit, post-index.
    pub fn ldr_x_post(&mut self, rt: Reg, rn: Reg, offset: i16) {
        let imm9 = (offset as u32) & 0x1FF;
        let inst = 0xF8400400 | imm9 << 12 | (rn.0 as u32 & 0x1F) << 5 | (rt.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    // ---- Population count helpers (SIMD) ----

    /// `FMOV Dd, Xn` — move general register to SIMD/FP register.
    pub fn fmov_d_from_x(&mut self, rd: Reg, rn: Reg) {
        let inst = 0x9E670000
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `FMOV Xd, Dn` — move SIMD/FP register to general register.
    pub fn fmov_x_from_d(&mut self, rd: Reg, rn: Reg) {
        let inst = 0x9E660000
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `CNT Vd.8B, Vn.8B` — count set bits per byte in SIMD register.
    pub fn cnt_8b(&mut self, rd: Reg, rn: Reg) {
        let inst = 0x0E205800
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `ADDV Bd, Vn.8B` — unsigned sum of 8B vector elements into scalar.
    pub fn addv_8b(&mut self, rd: Reg, rn: Reg) {
        let inst = 0x0E31B800
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    /// `UMOV Wd, Vn.B[0]` — extract byte 0 from SIMD register to GP register.
    pub fn umov_w_b0(&mut self, rd: Reg, rn: Reg) {
        let inst = 0x0E023C00
            | (rn.0 as u32 & 0x1F) << 5
            | (rd.0 as u32 & 0x1F);
        self.code.push(inst);
    }

    // ---- Branches ----

    /// `B <label>` — unconditional branch. Returns a PatchPoint for the target.
    pub fn b(&mut self) -> PatchPoint {
        let pp = PatchPoint {
            index: self.code.len(),
        };
        self.code.push(0x14000000); // placeholder, imm26 = 0
        pp
    }

    /// `B <offset>` — unconditional branch with known word offset.
    pub fn b_offset(&mut self, word_offset: i32) {
        let imm26 = (word_offset as u32) & 0x03FF_FFFF;
        self.code.push(0x14000000 | imm26);
    }

    /// `B.cond <offset>` — conditional branch with known word offset.
    pub fn b_cond_offset(&mut self, cond: Cond, word_offset: i32) {
        let imm19 = ((word_offset as u32) & 0x7FFFF) << 5;
        self.code.push(0x54000000 | imm19 | (cond as u32));
    }

    /// `B.cond <label>` — conditional branch. Returns a PatchPoint.
    pub fn b_cond(&mut self, cond: Cond) -> PatchPoint {
        let pp = PatchPoint {
            index: self.code.len(),
        };
        self.code.push(0x54000000 | (cond as u32)); // imm19 = 0
        pp
    }

    /// `BC.cond <label>` — branch consistent conditionally (FEAT_HBC).
    ///
    /// Hints to the branch predictor that this branch almost always goes
    /// the same direction. Encoding is B.cond with bit 4 set.
    pub fn bc_cond(&mut self, cond: Cond) -> PatchPoint {
        let pp = PatchPoint {
            index: self.code.len(),
        };
        self.code.push(0x54000010 | (cond as u32)); // bit 4 = 1 (consistent hint)
        pp
    }

    /// `CBZ Wt, <label>` — compare and branch if zero (32-bit).
    pub fn cbz_w(&mut self, rt: Reg) -> PatchPoint {
        let pp = PatchPoint {
            index: self.code.len(),
        };
        self.code.push(0x34000000 | (rt.0 as u32 & 0x1F));
        pp
    }

    /// `CBNZ Wt, <label>` — compare and branch if nonzero (32-bit).
    pub fn cbnz_w(&mut self, rt: Reg) -> PatchPoint {
        let pp = PatchPoint {
            index: self.code.len(),
        };
        self.code.push(0x35000000 | (rt.0 as u32 & 0x1F));
        pp
    }

    /// `CBNZ Xt, <label>` — compare and branch if nonzero (64-bit).
    pub fn cbnz_x(&mut self, rt: Reg) -> PatchPoint {
        let pp = PatchPoint {
            index: self.code.len(),
        };
        self.code.push(0xB5000000 | (rt.0 as u32 & 0x1F));
        pp
    }

    /// `BL <offset>` — branch with link (call), known word offset.
    pub fn bl_offset(&mut self, word_offset: i32) {
        let imm26 = (word_offset as u32) & 0x03FF_FFFF;
        self.code.push(0x94000000 | imm26);
    }

    /// `BLR Xn` — branch with link to register (indirect call).
    pub fn blr(&mut self, rn: Reg) {
        let inst = 0xD63F0000 | ((rn.0 as u32 & 0x1F) << 5);
        self.code.push(inst);
    }

    /// `BRK #imm16` — breakpoint.
    pub fn brk(&mut self, imm16: u16) {
        self.code.push(0xD4200000 | ((imm16 as u32) << 5));
    }

    /// `MOVK Wd, #imm16, LSL #shift` — move with keep (16-bit immediate).
    pub fn movk_w(&mut self, rd: Reg, imm16: u16, shift: u8) {
        debug_assert!(shift == 0 || shift == 16);
        let hw = (shift / 16) as u32;
        self.code
            .push(0x72800000 | (hw << 21) | ((imm16 as u32) << 5) | (rd.0 as u32 & 0x1F));
    }

    /// `CBZ Wt, <word_offset>` — compare and branch if zero, known offset.
    pub fn cbz_w_offset(&mut self, rt: Reg, word_offset: i32) {
        let imm19 = ((word_offset as u32) & 0x7FFFF) << 5;
        self.code.push(0x34000000 | imm19 | (rt.0 as u32 & 0x1F));
    }

    /// `CBNZ Wt, <word_offset>` — compare and branch if nonzero, known offset.
    pub fn cbnz_w_offset(&mut self, rt: Reg, word_offset: i32) {
        let imm19 = ((word_offset as u32) & 0x7FFFF) << 5;
        self.code.push(0x35000000 | imm19 | (rt.0 as u32 & 0x1F));
    }

    /// `RET` — return (branch to X30).
    pub fn ret(&mut self) {
        self.code.push(0xD65F03C0);
    }

    // ---- Patching ----

    /// Patch a branch instruction at `pp` to target the current offset.
    pub fn patch(&mut self, pp: PatchPoint) {
        let target = self.code.len();
        let source = pp.index;
        let word_offset = (target as i32) - (source as i32);
        let inst = self.code[source];
        let opcode_top = inst >> 24;

        self.code[source] = Self::patch_branch(inst, opcode_top, word_offset);
    }

    /// Patch a branch at `pp` to target a specific word offset (not current).
    pub fn patch_to(&mut self, pp: PatchPoint, target_word: usize) {
        let source = pp.index;
        let word_offset = (target_word as i32) - (source as i32);
        let inst = self.code[source];
        let opcode_top = inst >> 24;

        self.code[source] = Self::patch_branch(inst, opcode_top, word_offset);
    }

    fn patch_branch(inst: u32, opcode_top: u32, word_offset: i32) -> u32 {
        match opcode_top {
            // B: 0x14..0x17, BL: 0x94..0x97 — both use imm26
            0x14 | 0x15 | 0x16 | 0x17 => {
                let imm26 = (word_offset as u32) & 0x03FF_FFFF;
                0x14000000 | imm26
            }
            0x94 | 0x95 | 0x96 | 0x97 => {
                let imm26 = (word_offset as u32) & 0x03FF_FFFF;
                0x94000000 | imm26
            }
            // B.cond: 0x54
            0x54 => {
                let cond = inst & 0xF;
                let imm19 = ((word_offset as u32) & 0x7FFFF) << 5;
                0x54000000 | imm19 | cond
            }
            // CBZ (32-bit): 0x34, CBZ (64-bit): 0xB4
            0x34 | 0xB4 => {
                let base = (opcode_top & 0xFF) << 24;
                let rt = inst & 0x1F;
                let imm19 = ((word_offset as u32) & 0x7FFFF) << 5;
                base | imm19 | rt
            }
            // CBNZ (32-bit): 0x35, CBNZ (64-bit): 0xB5
            0x35 | 0xB5 => {
                let base = (opcode_top & 0xFF) << 24;
                let rt = inst & 0x1F;
                let imm19 = ((word_offset as u32) & 0x7FFFF) << 5;
                base | imm19 | rt
            }
            _ => panic!("unknown branch opcode to patch: 0x{:08x}", inst),
        }
    }
}
