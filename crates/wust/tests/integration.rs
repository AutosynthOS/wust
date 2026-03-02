use wust_codegen::code_buffer::CodeBuffer;
use wust_codegen::emit::{Cond, Emitter, PatchPoint, Reg};
use wust_core::module::{self, ModuleMeta};
use wust_core::Stack;

// ── Prototype types ─────────────────────────────────────────────────

struct Module {
    meta: ModuleMeta,
    jit: Jit,
}

impl Module {
    fn new(wasm: &[u8]) -> Result<Self, anyhow::Error> {
        let meta = module::parse(wasm)?;
        let jit = Jit::compile(&meta)?;
        Ok(Module { meta, jit })
    }
}

struct Instance<'a> {
    module: &'a Module,
    stack: Stack,
}

impl<'a> Instance<'a> {
    fn new(module: &'a Module) -> Result<Self, anyhow::Error> {
        let stack = Stack::new()?;
        Ok(Instance { module, stack })
    }

    fn call(&mut self, name: &str, args: &[i32]) -> Result<i32, anyhow::Error> {
        let func_idx = self
            .module
            .meta
            .exports
            .get(name)
            .ok_or_else(|| anyhow::anyhow!("export '{name}' not found"))?;
        let func = &self.module.meta.funcs[func_idx.0 as usize];
        let frame_size = (8 + func.locals.len() * 8).max(16);

        // Write args into the callee's frame (header at +0, locals at +8).
        for (i, &arg) in args.iter().enumerate() {
            self.stack.write_u64_at(8 + i * 8, arg as u64);
        }

        Ok(self.module.jit.call(&self.stack, func_idx.0 as usize))
    }
}

// ── JIT compiler ────────────────────────────────────────────────────

struct Jit {
    buf: CodeBuffer,
    func_offsets: Vec<usize>,
}

/// Tracks deferred out-of-line suspend stubs to emit after the hot path.
struct SuspendStub {
    /// Branch patch point in the hot path (b.le → this stub).
    patch: PatchPoint,
    /// Resume point ID for the frame header.
    resume_point: u32,
    /// Function index (for the frame header).
    func_idx: u32,
    /// Which locals are live and need spilling at this point.
    /// For now: spill ALL locals unconditionally.
    local_count: usize,
}

impl Jit {
    fn compile(meta: &ModuleMeta) -> Result<Self, anyhow::Error> {
        let mut e = Emitter::new();
        let mut func_offsets = Vec::new();

        for (i, _func) in meta.funcs.iter().enumerate() {
            func_offsets.push(e.offset());
            Self::emit_func(&mut e, meta, i, &func_offsets);
        }

        let mut buf = CodeBuffer::new(e.code().len() * 4 + 64)?;
        for &word in e.code() {
            buf.emit_u32(word);
        }
        buf.finalize()?;

        Ok(Jit { buf, func_offsets })
    }

    /// Emit a single function.
    ///
    /// Walks raw WASM body bytes and emits ARM64 with:
    /// - fuel checks (subs x21, #cost; b.le suspend) in the hot path
    /// - out-of-line suspend stubs after the epilogue
    ///
    /// Register usage:
    ///   x9  = first local / first result
    ///   x10 = second local
    ///   x11 = third local (and scratch)
    ///   x29 = wasm frame pointer
    ///   x21 = fuel (pinned)
    fn emit_func(e: &mut Emitter, meta: &ModuleMeta, func_idx: usize, offsets: &[usize]) {
        let func = &meta.funcs[func_idx];
        let body = &func.body_bytes;
        let local_count = func.locals.len();
        let mut pc = 0;
        let mut resume_point: u32 = 0;
        let mut suspend_stubs: Vec<SuspendStub> = Vec::new();

        // Frame layout: [header 8B] [local0 8B] [local1 8B] ...
        // Header at [x29 + 0], locals at [x29 + 8], [x29 + 16], ...
        let header_offset: u16 = 0;
        let local_offset = |idx: usize| -> u16 { (8 + idx * 8) as u16 };
        let frame_size = (8 + local_count * 8).max(16) as u16;

        // Prologue: save lr on native stack.
        let has_calls = body.iter().any(|&b| b == 0x10);
        if has_calls {
            e.str_x_pre(Reg::X30, Reg::SP, -16);
        }

        // Load params from frame into registers (resume point 0).
        // For a fresh call, the trampoline or caller has written args
        // to our frame. We load them into x9, x10, ...
        for i in 0..func.param_count.min(7) {
            let reg = Reg(9 + i as u8);
            e.ldr_x_uoff(reg, Reg::X29, local_offset(i));
        }

        while pc < body.len() {
            match body[pc] {
                // i32.const (0x41)
                0x41 => {
                    pc += 1;
                    let (val, len) = read_leb128_i32(&body[pc..]);
                    pc += len;
                    // Push onto register "stack" — for now just use x9
                    // since our test functions are simple enough.
                    // TODO: proper register allocation
                    e.movz_x(Reg::X9, val as u16);
                }

                // local.get (0x20)
                0x20 => {
                    pc += 1;
                    let (idx, len) = read_leb128_u32(&body[pc..]);
                    pc += len;
                    let src = Reg(9 + idx as u8);
                    // Move to x9 (result position). Nop if already x9.
                    if src.0 != 9 {
                        e.mov_x(Reg::X9, src);
                    }
                }

                // local.set (0x21)
                0x21 => {
                    pc += 1;
                    let (idx, len) = read_leb128_u32(&body[pc..]);
                    pc += len;
                    let dst = Reg(9 + idx as u8);
                    if dst.0 != 9 {
                        e.mov_x(dst, Reg::X9);
                    }
                }

                // i32.add (0x6A)
                0x6A => {
                    pc += 1;
                    // x9 = x10 + x9 (second operand + first operand)
                    e.add_w(Reg::X9, Reg::X10, Reg::X9);
                }

                // i32.sub (0x6B)
                0x6B => {
                    pc += 1;
                    e.sub_w(Reg::X9, Reg::X10, Reg::X9);
                }

                // i32.lt_s (0x48)
                0x48 => {
                    pc += 1;
                    e.cmp_w_reg(Reg::X10, Reg::X9);
                    e.cset_w(Reg::X9, Cond::LT);
                }

                // call (0x10)
                0x10 => {
                    pc += 1;
                    let (callee_idx, len) = read_leb128_u32(&body[pc..]);
                    pc += len;

                    let callee = &meta.funcs[callee_idx as usize];
                    let callee_frame = (8 + callee.locals.len() * 8).max(16) as u16;

                    // Spill live locals to frame before call.
                    for i in 0..local_count.min(7) {
                        let reg = Reg(9 + i as u8);
                        e.str_x_uoff(reg, Reg::X29, local_offset(i));
                    }

                    // Fuel check before call.
                    e.subs_x_imm(Reg::X21, Reg::X21, 1);
                    let suspend_branch = e.b_cond(Cond::LE);
                    suspend_stubs.push(SuspendStub {
                        patch: suspend_branch,
                        resume_point,
                        func_idx: func_idx as u32,
                        local_count,
                    });
                    resume_point += 1;

                    // Write callee's args to callee's frame.
                    // For now: single arg in x9 → callee's local 0.
                    let callee_local0_offset = 8u16; // [callee_fp + 8]
                    e.str_x_uoff(Reg::X9, Reg::X29, frame_size + callee_local0_offset);

                    // Call.
                    e.add_x_imm(Reg::X29, Reg::X29, frame_size);
                    let bl_target = offsets[callee_idx as usize] as i32 - e.offset() as i32;
                    e.bl_offset(bl_target);
                    e.sub_x_imm(Reg::X29, Reg::X29, frame_size);

                    // Reload locals from frame after call.
                    for i in 0..local_count.min(7) {
                        let reg = Reg(9 + i as u8);
                        e.ldr_x_uoff(reg, Reg::X29, local_offset(i));
                    }
                }

                // loop (0x03) — fuel check at loop header
                0x03 => {
                    pc += 1;
                    let (_block_type, len) = read_leb128_i32(&body[pc..]);
                    pc += len;

                    // Spill locals before fuel check.
                    for i in 0..local_count.min(7) {
                        let reg = Reg(9 + i as u8);
                        e.str_x_uoff(reg, Reg::X29, local_offset(i));
                    }

                    // Fuel check at loop header.
                    e.subs_x_imm(Reg::X21, Reg::X21, 1);
                    let suspend_branch = e.b_cond(Cond::LE);
                    suspend_stubs.push(SuspendStub {
                        patch: suspend_branch,
                        resume_point,
                        func_idx: func_idx as u32,
                        local_count,
                    });
                    resume_point += 1;
                }

                // br (0x0C)
                0x0C => {
                    pc += 1;
                    let (_depth, len) = read_leb128_u32(&body[pc..]);
                    pc += len;
                    // TODO: branch target resolution
                    // For now this is a stub.
                }

                // br_if (0x0D)
                0x0D => {
                    pc += 1;
                    let (_depth, len) = read_leb128_u32(&body[pc..]);
                    pc += len;
                    // TODO: conditional branch
                }

                // block (0x02)
                0x02 => {
                    pc += 1;
                    let (_block_type, len) = read_leb128_i32(&body[pc..]);
                    pc += len;
                }

                // if (0x04)
                0x04 => {
                    pc += 1;
                    let (_block_type, len) = read_leb128_i32(&body[pc..]);
                    pc += len;
                    // TODO: conditional
                }

                // else (0x05)
                0x05 => {
                    pc += 1;
                }

                // end (0x0B)
                0x0B => {
                    pc += 1;
                }

                // return (0x0F)
                0x0F => {
                    pc += 1;
                }

                other => {
                    todo!("opcode 0x{other:02x} not implemented in fake JIT");
                }
            }
        }

        // Epilogue: fuel decrement for the return path.
        e.subs_x_imm(Reg::X21, Reg::X21, 1);
        if has_calls {
            e.ldr_x_post(Reg::X30, Reg::SP, 16);
        }
        e.ret();

        // ── Out-of-line suspend stubs ───────────────────────────────
        //
        // Each stub:
        //   1. Spills all locals to frame (may already be spilled)
        //   2. Writes frame header: func_idx | resume_point packed in u64
        //   3. Pops lr if needed
        //   4. Returns (callee will unwind back to trampoline)
        //
        // These are cold paths — never executed with infinite fuel.
        for stub in &suspend_stubs {
            e.patch(stub.patch);

            // Spill locals to frame.
            for i in 0..stub.local_count.min(7) {
                let reg = Reg(9 + i as u8);
                e.str_x_uoff(reg, Reg::X29, local_offset(i));
            }

            // Write frame header: pack func_idx (high 32) | resume_point (low 32).
            // Use x0 as scratch (not in our register set).
            let header = ((stub.func_idx as u64) << 32) | stub.resume_point as u64;
            e.movz_x(Reg::X0, header as u16);
            if header > 0xFFFF {
                // TODO: movk for larger values
            }
            e.str_x_uoff(Reg::X0, Reg::X29, header_offset);

            // Epilogue.
            if has_calls {
                e.ldr_x_post(Reg::X30, Reg::SP, 16);
            }
            e.ret();
        }
    }

    fn call(&self, stack: &Stack, func_idx: usize) -> i32 {
        let func_word_offset = self.func_offsets[func_idx];
        let func_ptr = unsafe { self.buf.entry().add(func_word_offset * 4) };
        let frame_base = stack.base() as u64;
        let fuel = i64::MAX as u64;

        let result: u64;
        unsafe {
            std::arch::asm!(
                "stp x29, x30, [sp, #-16]!",
                "stp x20, x21, [sp, #-16]!",

                "mov x29, {frame_base}",
                "mov x21, {fuel}",
                "blr {code}",
                "mov {result}, x9",

                "ldp x20, x21, [sp], #16",
                "ldp x29, x30, [sp], #16",

                frame_base = in(reg) frame_base,
                fuel = in(reg) fuel,
                code = in(reg) func_ptr,
                result = out(reg) result,
                out("x9") _, out("x10") _, out("x11") _,
                out("x12") _, out("x13") _, out("x14") _,
                out("x15") _,
            );
        }

        result as i32
    }
}

// ── LEB128 helpers ──────────────────────────────────────────────────

fn read_leb128_i32(bytes: &[u8]) -> (i32, usize) {
    let mut result: i32 = 0;
    let mut shift = 0;
    let mut pos = 0;
    loop {
        let byte = bytes[pos];
        pos += 1;
        result |= ((byte & 0x7F) as i32) << shift;
        shift += 7;
        if byte & 0x80 == 0 {
            if shift < 32 && (byte & 0x40) != 0 {
                result |= !0 << shift;
            }
            return (result, pos);
        }
    }
}

fn read_leb128_u32(bytes: &[u8]) -> (u32, usize) {
    let mut result: u32 = 0;
    let mut shift = 0;
    let mut pos = 0;
    loop {
        let byte = bytes[pos];
        pos += 1;
        result |= ((byte & 0x7F) as u32) << shift;
        shift += 7;
        if byte & 0x80 == 0 {
            return (result, pos);
        }
    }
}

// ── Tests ───────────────────────────────────────────────────────────

#[test]
fn call_add_42_times() -> Result<(), anyhow::Error> {
    // $add(a, b) -> a + b
    // $answer(x) -> $add(x, 100)
    let wasm = wat::parse_str(
        r#"
        (module
            (func $add (param $a i32) (param $b i32) (result i32)
                local.get $a
                local.get $b
                i32.add
            )
            (func (export "answer") (param $x i32) (result i32)
                local.get $x
                i32.const 100
                call $add
            )
        )
    "#,
    )?;

    let module = Module::new(&wasm)?;
    let mut inst = Instance::new(&module)?;
    let result = inst.call("answer", &[42])?;
    assert_eq!(result, 142);

    Ok(())
}
