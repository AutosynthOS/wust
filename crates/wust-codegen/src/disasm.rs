use std::fmt::Write;

/// Output of the codegen pipeline for a single function.
pub struct FunctionOutput {
    /// The IR text (always available).
    pub ir: String,
    /// Raw u32 instruction words.
    pub code: Vec<u32>,
    /// Word-offset markers: prologue, each IR instruction, yield, completion.
    pub markers: Vec<usize>,
    /// Number of IR instructions (for mapping markers to regions).
    pub ir_inst_count: usize,
}

/// Output of the codegen pipeline for a module.
pub struct CodegenOutput {
    pub functions: Vec<(String, FunctionOutput)>,
}

impl CodegenOutput {
    /// Render an annotated inspection view.
    ///
    /// Each IR instruction is shown as a comment, followed by the asm
    /// words it produced, with hex encoding.
    pub fn render_inspect(&self) -> String {
        let mut out = String::new();

        for (name, func) in &self.functions {
            writeln!(out, ";;; func {name}").unwrap();
            writeln!(out).unwrap();

            let markers = &func.markers;
            let total_words = func.code.len();

            let ir_lines: Vec<&str> = func.ir.lines().collect();

            for region_idx in 0..markers.len() {
                let start = markers[region_idx];
                let end = if region_idx + 1 < markers.len() {
                    markers[region_idx + 1]
                } else {
                    total_words
                };

                if start == end {
                    continue;
                }

                let label = region_label(region_idx, func.ir_inst_count, &ir_lines);
                writeln!(out, "  ;; {label}").unwrap();

                for word_idx in start..end {
                    let word = func.code[word_idx];
                    let byte_off = word_idx * 4;
                    writeln!(out, "    {byte_off:04x}: {word:08x}  {}", disasm(word)).unwrap();
                }
                writeln!(out).unwrap();
            }
        }

        out
    }
}

/// Determine the label for a region based on its index.
///
/// Layout: [prologue] [IR inst 0] [IR inst 1] ... [IR inst N-1] [yield] [completion]
fn region_label<'a>(region_idx: usize, ir_inst_count: usize, ir_lines: &[&'a str]) -> &'a str {
    if region_idx == 0 {
        return "prologue";
    }

    let ir_idx = region_idx - 1;
    if ir_idx < ir_inst_count {
        let line_idx = ir_idx + 1;
        if line_idx < ir_lines.len() {
            return ir_lines[line_idx].trim();
        }
        return "???";
    }

    let tail_idx = ir_idx - ir_inst_count;
    match tail_idx {
        0 => "yield handler",
        1 => "completion handler",
        _ => "???",
    }
}

/// Format a register as xN, or "sp" when register 31 is used as a base address.
fn xreg(r: u8) -> String {
    if r == 31 {
        "sp".to_string()
    } else {
        format!("x{r}")
    }
}

/// Format a register as xN, or "xzr" when register 31 is used as a zero source.
fn xreg_or_zr(r: u8) -> String {
    if r == 31 {
        "xzr".to_string()
    } else {
        format!("x{r}")
    }
}

/// Minimal aarch64 disassembler for the instruction subset we emit.
pub fn disasm(word: u32) -> String {
    let rd = (word & 0x1F) as u8;
    let rn = ((word >> 5) & 0x1F) as u8;
    let rt = rd;
    let rt2 = ((word >> 10) & 0x1F) as u8;

    // STP/LDP (64-bit, pre-index / post-index / signed offset)
    if word & 0xFFC00000 == 0xA9800000 {
        let offset = sign_extend(((word >> 15) & 0x7F) as i32, 7) * 8;
        return format!("stp x{rt}, x{rt2}, [{}, #{offset}]!", xreg(rn));
    }
    if word & 0xFFC00000 == 0xA8C00000 {
        let offset = sign_extend(((word >> 15) & 0x7F) as i32, 7) * 8;
        return format!("ldp x{rt}, x{rt2}, [{}], #{offset}", xreg(rn));
    }
    if word & 0xFFC00000 == 0xA9000000 {
        let offset = sign_extend(((word >> 15) & 0x7F) as i32, 7) * 8;
        return format!("stp x{rt}, x{rt2}, [{}, #{offset}]", xreg(rn));
    }
    if word & 0xFFC00000 == 0xA9400000 {
        let offset = sign_extend(((word >> 15) & 0x7F) as i32, 7) * 8;
        return format!("ldp x{rt}, x{rt2}, [{}, #{offset}]", xreg(rn));
    }

    // LDR x, unsigned offset
    if word & 0xFFC00000 == 0xF9400000 {
        let imm12 = ((word >> 10) & 0xFFF) as u16;
        let offset = imm12 * 8;
        return format!("ldr {}, [{}, #{offset}]", xreg_or_zr(rt), xreg(rn));
    }
    // STR x, unsigned offset
    if word & 0xFFC00000 == 0xF9000000 {
        let imm12 = ((word >> 10) & 0xFFF) as u16;
        let offset = imm12 * 8;
        return format!("str {}, [{}, #{offset}]", xreg_or_zr(rt), xreg(rn));
    }

    // ADD w, immediate
    if word & 0xFF000000 == 0x11000000 {
        let imm12 = (word >> 10) & 0xFFF;
        return format!("add w{rd}, w{rn}, #{imm12}");
    }
    // SUB w, immediate
    if word & 0xFF000000 == 0x51000000 {
        let imm12 = (word >> 10) & 0xFFF;
        return format!("sub w{rd}, w{rn}, #{imm12}");
    }
    // CMP w, immediate (SUBS wzr, wn, #imm12)
    if word & 0xFF000000 == 0x71000000 {
        let imm12 = (word >> 10) & 0xFFF;
        if rd == 31 {
            return format!("cmp w{rn}, #{imm12}");
        }
        return format!("subs w{rd}, w{rn}, #{imm12}");
    }
    // ADD x, immediate
    if word & 0xFF000000 == 0x91000000 {
        let imm12 = (word >> 10) & 0xFFF;
        let shift = if (word >> 22) & 1 == 1 { 12 } else { 0 };
        let val = imm12 << shift;
        return format!("add {}, {}, #{val}", xreg(rd), xreg(rn));
    }
    // SUB x, immediate
    if word & 0xFF000000 == 0xD1000000 {
        let imm12 = (word >> 10) & 0xFFF;
        return format!("sub {}, {}, #{imm12}", xreg(rd), xreg(rn));
    }
    // SUBS x, immediate
    if word & 0xFF000000 == 0xF1000000 {
        let imm12 = (word >> 10) & 0xFFF;
        return format!("subs x{rd}, x{rn}, #{imm12}");
    }

    // ADD w, register
    if word & 0xFFE00000 == 0x0B000000 {
        let rm = ((word >> 16) & 0x1F) as u8;
        return format!("add w{rd}, w{rn}, w{rm}");
    }
    // SUB w, register
    if word & 0xFFE00000 == 0x4B000000 {
        let rm = ((word >> 16) & 0x1F) as u8;
        return format!("sub w{rd}, w{rn}, w{rm}");
    }
    // SUB x, register
    if word & 0xFFE00000 == 0xCB000000 {
        let rm = ((word >> 16) & 0x1F) as u8;
        return format!("sub x{rd}, x{rn}, x{rm}");
    }
    // CMP w, register (SUBS wzr)
    if word & 0xFFE0001F == 0x6B00001F {
        let rm = ((word >> 16) & 0x1F) as u8;
        return format!("cmp w{rn}, w{rm}");
    }

    // CSINC w
    if word & 0xFFE00C00 == 0x1A800400 {
        let rm = ((word >> 16) & 0x1F) as u8;
        let cond_bits = ((word >> 12) & 0xF) as u8;
        if rn == 31 && rm == 31 {
            let cond = cond_name(cond_bits ^ 1);
            return format!("cset w{rd}, {cond}");
        }
        let cond = cond_name(cond_bits);
        return format!("csinc w{rd}, w{rn}, w{rm}, {cond}");
    }

    // MOVZ / MOVN (immediate)
    if word & 0xFF800000 == 0x52800000 {
        let imm16 = (word >> 5) & 0xFFFF;
        return format!("mov w{rd}, #{imm16}");
    }
    if word & 0xFF800000 == 0x12800000 {
        let imm16 = (word >> 5) & 0xFFFF;
        let val = !(imm16 as i32);
        return format!("mov w{rd}, #{val}");
    }
    if word & 0xFF800000 == 0xD2800000 {
        let imm16 = (word >> 5) & 0xFFFF;
        return format!("mov x{rd}, #{imm16}");
    }

    // MOV x (ORR xd, xzr, xn)
    if word & 0xFFE0FFE0 == 0xAA0003E0 {
        let rm = ((word >> 16) & 0x1F) as u8;
        return format!("mov x{rd}, x{rm}");
    }

    // CBZ w
    if word & 0xFF000000 == 0x34000000 {
        let imm19 = ((word >> 5) & 0x7FFFF) as i32;
        let offset = sign_extend(imm19, 19) * 4;
        return format!("cbz w{rt}, .{offset:+}");
    }
    // CBNZ w
    if word & 0xFF000000 == 0x35000000 {
        let imm19 = ((word >> 5) & 0x7FFFF) as i32;
        let offset = sign_extend(imm19, 19) * 4;
        return format!("cbnz w{rt}, .{offset:+}");
    }
    // CBZ x
    if word & 0xFF000000 == 0xB4000000 {
        let imm19 = ((word >> 5) & 0x7FFFF) as i32;
        let offset = sign_extend(imm19, 19) * 4;
        return format!("cbz x{rt}, .{offset:+}");
    }
    // CBNZ x
    if word & 0xFF000000 == 0xB5000000 {
        let imm19 = ((word >> 5) & 0x7FFFF) as i32;
        let offset = sign_extend(imm19, 19) * 4;
        return format!("cbnz x{rt}, .{offset:+}");
    }

    // B (unconditional)
    if word & 0xFC000000 == 0x14000000 {
        let imm26 = (word & 0x3FFFFFF) as i32;
        let offset = sign_extend(imm26, 26) * 4;
        return format!("b .{offset:+}");
    }
    // BL
    if word & 0xFC000000 == 0x94000000 {
        let imm26 = (word & 0x3FFFFFF) as i32;
        let offset = sign_extend(imm26, 26) * 4;
        return format!("bl .{offset:+}");
    }
    // B.cond
    if word & 0xFF000010 == 0x54000000 {
        let imm19 = ((word >> 5) & 0x7FFFF) as i32;
        let offset = sign_extend(imm19, 19) * 4;
        let cond = cond_name((word & 0xF) as u8);
        return format!("b.{cond} .{offset:+}");
    }

    // BLR
    if word & 0xFFFFFC1F == 0xD63F0000 {
        return format!("blr x{rn}");
    }
    // BR
    if word & 0xFFFFFC1F == 0xD61F0000 {
        return format!("br x{rn}");
    }
    // RET
    if word == 0xD65F03C0 {
        return "ret".to_string();
    }

    // BRK
    if word & 0xFFE0001F == 0xD4200000 {
        let imm16 = (word >> 5) & 0xFFFF;
        return format!("brk #{imm16}");
    }

    format!(".word 0x{word:08x}")
}

fn sign_extend(val: i32, bits: u32) -> i32 {
    let shift = 32 - bits;
    (val << shift) >> shift
}

fn cond_name(cond: u8) -> &'static str {
    match cond & 0xF {
        0x0 => "eq",
        0x1 => "ne",
        0x2 => "cs",
        0x3 => "cc",
        0x4 => "mi",
        0x5 => "pl",
        0x6 => "vs",
        0x7 => "vc",
        0x8 => "hi",
        0x9 => "ls",
        0xA => "ge",
        0xB => "lt",
        0xC => "gt",
        0xD => "le",
        0xE => "al",
        _ => "??",
    }
}
