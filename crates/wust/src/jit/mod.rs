pub mod codegen;
pub(crate) mod compiler;
#[cfg(test)]
pub(crate) mod tests;

use crate::Instance;
use crate::Module;
use crate::stack::Stack;
use crate::value::WasmArgs;

use wust_codegen::code_buffer::CodeBuffer;
use wust_codegen::context::JitContext;
use wust_codegen::emit;
use wust_codegen::lower_aarch64;
use wust_codegen::lower_aarch64::SharedHandlerOffsets;

/// A JIT-compiled module with a shared code buffer.
///
/// All functions live in a single mmap'd region. A jump table at the
/// start dispatches calls via PC-relative branches — no indirect
/// loads, no runtime function table.
pub struct JitModule {
    /// Single code buffer containing all compiled code.
    buffer: CodeBuffer,
    /// Number of functions in the module.
    func_count: usize,
    /// Shared handler offsets (word offsets within the buffer).
    shared: SharedHandlerOffsets,
}

// The compiled code buffer is mmap'd memory — safe to send across threads.
unsafe impl Send for JitModule {}
unsafe impl Sync for JitModule {}

/// Builder for JIT compilation.
///
/// Configures how wasm functions are compiled to native code.
///
/// # Examples
///
/// ```ignore
/// // Default (fuel enabled):
/// let jit = JitCompiler::new(&module).compile()?;
///
/// // Without fuel checks (faster, but cannot suspend):
/// let jit = JitCompiler::new(&module).fuel(false).compile()?;
/// ```
pub struct JitCompiler<'a> {
    module: &'a Module,
    emit_fuel: bool,
}

impl<'a> JitCompiler<'a> {
    pub fn new(module: &'a Module) -> Self {
        JitCompiler {
            module,
            emit_fuel: true,
        }
    }

    /// Enable or disable fuel check emission.
    ///
    /// When disabled, compiled code runs to completion without
    /// suspension points. Produces faster code but fibers cannot
    /// yield mid-execution.
    pub fn fuel(mut self, enabled: bool) -> Self {
        self.emit_fuel = enabled;
        self
    }

    /// Compile all functions into a shared code buffer.
    ///
    /// Layout: [jump table][interpret stubs][shared handlers][fn0][fn1]...
    pub fn compile(self) -> Result<JitModule, anyhow::Error> {
        let func_count = self.module.funcs.len();
        let mut e = emit::Emitter::new();

        // Emit shared preamble: jump table, interpret stubs, handlers.
        let shared = lower_aarch64::emit_shared_preamble(&mut e, func_count);

        // Track body offsets for direct BL optimization.
        let mut body_offsets: Vec<Option<usize>> = vec![None; func_count];

        // Compile and append each function body.
        for (i, func) in self.module.funcs.iter().enumerate() {
            let ir = compiler::compile_with(func, &self.module.funcs, self.emit_fuel);
            let layout =
                lower_aarch64::lower_into(&mut e, &ir, i as u32, &shared, &mut body_offsets, false);
            // Patch jump table entry to point at the compiled body.
            let body_word = layout.body_offset / 4;
            lower_aarch64::patch_jump_table(&mut e, i as u32, body_word);
        }

        // Copy emitter output into executable CodeBuffer.
        let mut buffer = CodeBuffer::new(e.code().len() * 4 + 64)?;
        for &word in e.code() {
            buffer.emit_u32(word);
        }
        buffer.finalize()?;

        Ok(JitModule {
            buffer,
            func_count,
            shared,
        })
    }
}

impl JitModule {
    /// Compile all functions in a module with default settings (fuel enabled).
    ///
    /// Pipeline: wasm ops → IR (virtual registers) → aarch64 machine code.
    pub fn compile(module: &Module) -> Result<Self, anyhow::Error> {
        JitCompiler::new(module).compile()
    }

    /// Call a compiled function by export name (non-fiber, unlimited fuel).
    pub fn call<A: WasmArgs>(
        &self,
        instance: &mut Instance,
        name: &str,
        args: A,
    ) -> Result<i32, anyhow::Error> {
        let func_idx = instance.resolve_export_func_idx(name)?;
        let stack = &mut instance.stack;

        // Push args onto the wasm stack.
        stack.set_sp(0);
        for val in args.to_vals() {
            stack.push_val(&val);
        }

        let result = unsafe { self.enter(func_idx.0 as usize, stack) };
        Ok(result)
    }

    /// Create a fiber for calling a function with bounded fuel.
    ///
    /// The fiber can be suspended and resumed, allowing cooperative
    /// multitasking and bounded execution.
    pub fn fiber<A: WasmArgs>(
        &self,
        instance: &mut Instance,
        name: &str,
        args: A,
    ) -> Result<JitFiber, anyhow::Error> {
        let func_idx = instance.resolve_export_func_idx(name)?;
        let stack = &mut instance.stack;

        stack.set_sp(0);
        for val in args.to_vals() {
            stack.push_val(&val);
        }

        // Entry via jump table.
        let code_ptr = self.jump_table_entry(func_idx.0 as usize);
        // Shared completion handler.
        let completion_ptr = self.shared_handler_ptr(self.shared.completion);

        // Load args from wasm stack for register passing.
        let num_args = stack.sp() / 8;
        let mut arg_regs = [0u64; 7];
        for i in 0..num_args.min(7) {
            arg_regs[i] = stack.read_u64_at(i * 8);
        }

        let mut ctx = JitContext::new();
        ctx.stack_base = stack.base() as u64;
        ctx.is_fiber = 1;

        Ok(JitFiber {
            ctx,
            jit_stack: JitStack::new(1024 * 1024)?, // 1MB native stack
            code_ptr,
            completion_ptr,
            frame_base: stack.base() as u64,
            arg_regs,
            status: FiberStatus::Ready,
        })
    }

    /// Pointer to jump table entry for a given function index.
    fn jump_table_entry(&self, func_idx: usize) -> *const u8 {
        debug_assert!(func_idx < self.func_count);
        unsafe { self.buffer.entry().add(func_idx * 4) }
    }

    /// Pointer to a shared handler at a given word offset.
    fn shared_handler_ptr(&self, word_offset: usize) -> *const u8 {
        unsafe { self.buffer.entry().add(word_offset * 4) }
    }

    /// Enter JIT code for a function (non-fiber mode).
    ///
    /// Sets x20=ctx, x21=fuel, x29=frame base, passes args in x9-x15.
    /// Result is returned in x9.
    unsafe fn enter(&self, func_idx: usize, stack: &mut Stack) -> i32 {
        let code_ptr = self.jump_table_entry(func_idx);
        let base = stack.base();
        let fuel: i64 = i64::MAX;

        let mut ctx = JitContext::new();
        ctx.stack_base = base as u64;

        let ctx_ptr = &mut ctx as *mut JitContext;

        // Load up to 7 args from the wasm stack.
        let num_args = stack.sp() / 8;
        let mut args = [0u64; 7];
        for i in 0..num_args.min(7) {
            args[i] = stack.read_u64_at(i * 8);
        }

        let result: i64;
        unsafe {
            std::arch::asm!(
                "stp x29, x30, [sp, #-16]!",
                "mov x20, x0",
                "mov x21, x1",
                "mov x29, x2",
                // Write prev_fp sentinel at [x29, #0] for the outermost frame.
                "str x29, [x29, #0]",
                "mov x3, x8",
                "blr x3",
                "mov x0, x9",
                "ldp x29, x30, [sp], #16",
                in("x0") ctx_ptr as u64,
                in("x1") fuel as u64,
                in("x2") base as u64,
                in("x8") code_ptr as u64,
                in("x9") args[0],
                in("x10") args[1],
                in("x11") args[2],
                in("x12") args[3],
                in("x13") args[4],
                in("x14") args[5],
                in("x15") args[6],
                lateout("x0") result,
                lateout("x1") _, lateout("x2") _, lateout("x3") _,
                lateout("x8") _,
                lateout("x9") _, lateout("x10") _,
                lateout("x11") _, lateout("x12") _,
                lateout("x13") _, lateout("x14") _,
                lateout("x15") _,
                out("x20") _, out("x21") _,
                out("x30") _,
            );
        }

        result as i32
    }
}

// ---- Fiber types ----

/// Result of a fiber resume.
pub enum FiberResult {
    /// The function completed normally. Contains the i32 result.
    Complete(i32),
    /// Fuel was exhausted. Call `resume()` with more fuel to continue.
    Suspended,
}

/// Status of a JIT fiber.
enum FiberStatus {
    /// Ready for first entry (hasn't started yet).
    Ready,
    /// Suspended mid-execution (can be resumed).
    Suspended,
    /// Completed (no further resumes possible).
    Complete,
}


/// A separate native stack for JIT code execution.
///
/// Allocated via mmap so we get proper page alignment.
struct JitStack {
    base: *mut u8, // bottom of allocated region
    size: usize,
}

impl JitStack {
    fn new(size: usize) -> Result<Self, anyhow::Error> {
        let base = unsafe {
            libc::mmap(
                std::ptr::null_mut(),
                size,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_PRIVATE | libc::MAP_ANONYMOUS,
                -1,
                0,
            )
        };
        if base == libc::MAP_FAILED {
            anyhow::bail!("mmap failed for JIT stack");
        }
        Ok(JitStack {
            base: base as *mut u8,
            size,
        })
    }

    /// Top of the stack (initial SP value — stacks grow downward).
    /// Aligned to 16 bytes as required by aarch64 ABI.
    fn top(&self) -> *mut u8 {
        unsafe { self.base.add(self.size & !0xF) }
    }
}

impl Drop for JitStack {
    fn drop(&mut self) {
        unsafe {
            libc::munmap(self.base as *mut libc::c_void, self.size);
        }
    }
}

/// A suspendable JIT execution fiber.
///
/// Runs JIT-compiled code on a separate native stack. When fuel runs
/// out, the fiber suspends, preserving the entire call chain. Calling
/// `resume()` with fresh fuel continues from exactly where it left off.
pub struct JitFiber {
    ctx: JitContext,
    jit_stack: JitStack,
    code_ptr: *const u8,
    completion_ptr: *const u8,
    frame_base: u64,
    arg_regs: [u64; 7],
    status: FiberStatus,
}

impl JitFiber {
    /// Resume (or start) execution with the given fuel budget.
    ///
    /// Returns `Complete(result)` when the function finishes, or
    /// `Suspended` when fuel runs out (call `resume` again to continue).
    pub fn resume(&mut self, fuel: i64) -> FiberResult {
        match self.status {
            FiberStatus::Complete => panic!("cannot resume a completed fiber"),
            FiberStatus::Ready => {
                self.status = FiberStatus::Suspended; // will be updated below
                let status = unsafe { self.fiber_start(fuel) };
                self.finish(status)
            }
            FiberStatus::Suspended => {
                let status = unsafe { self.fiber_resume(fuel) };
                self.finish(status)
            }
        }
    }

    fn finish(&mut self, status: u32) -> FiberResult {
        match status {
            0 => {
                self.status = FiberStatus::Suspended;
                FiberResult::Suspended
            }
            1 => {
                self.status = FiberStatus::Complete;
                // Read result from context (saved by completion handler).
                let result = self.ctx.wasm_sp_off as i32; // repurposed as result_value
                FiberResult::Complete(result)
            }
            _ => panic!("unexpected fiber status: {status}"),
        }
    }

    /// First entry into JIT code via fiber.
    ///
    /// 1. Saves host state (sp, fp, lr, x20) to JitContext.
    /// 2. Switches sp to the JIT stack.
    /// 3. Sets x20=ctx, x21=fuel, x30=completion.
    /// 4. Branches to function entry.
    ///
    /// Returns when the yield handler or completion handler switches
    /// back to the host stack: 0 = suspended, 1 = complete.
    unsafe fn fiber_start(&mut self, fuel: i64) -> u32 {
        let ctx_ptr = &mut self.ctx as *mut JitContext;
        let jit_sp = self.jit_stack.top();
        let completion = self.completion_ptr;
        let code = self.code_ptr;
        let frame_base = self.frame_base;
        let status: u32;

        unsafe {
            std::arch::asm!(
                // Save host state to JitContext.
                // x0=ctx, x1=jit_sp, x2=fuel, x3=completion, x4=code, x5=frame_base
                "adr x6, 2f",
                "stp x29, x6, [x0, #72]",    // host_fp + host_lr (landing pad)
                "mov x6, sp",
                "str x6, [x0, #64]",          // host_sp
                "str x20, [x0, #88]",         // host_ctx

                // Switch to JIT stack.
                "mov sp, x1",

                // Set up pinned registers.
                "mov x20, x0",
                "mov x21, x2",
                "mov x29, x5",
                // Write prev_fp sentinel at [x29, #0] for the outermost frame.
                "str x29, [x29, #0]",

                // Set lr = completion handler, then enter JIT.
                // x9-x15 already hold the args from in() constraints.
                "mov x30, x3",
                "br x4",

                // Landing pad: yield/completion handler restored host state
                // and did `ret`, which jumps here (host_lr = this address).
                "2:",

                in("x0") ctx_ptr as u64,
                in("x1") jit_sp as u64,
                in("x2") fuel as u64,
                in("x3") completion as u64,
                in("x4") code as u64,
                in("x5") frame_base,
                in("x9") self.arg_regs[0],
                in("x10") self.arg_regs[1],
                in("x11") self.arg_regs[2],
                in("x12") self.arg_regs[3],
                in("x13") self.arg_regs[4],
                in("x14") self.arg_regs[5],
                in("x15") self.arg_regs[6],
                lateout("x0") status,
                lateout("x1") _, lateout("x2") _,
                lateout("x3") _, lateout("x4") _,
                lateout("x5") _, lateout("x6") _,
                lateout("x9") _, lateout("x10") _,
                lateout("x11") _, lateout("x12") _,
                lateout("x13") _, lateout("x14") _,
                lateout("x15") _,
                out("x20") _, out("x21") _,
                out("x30") _,
            );
        }

        status as u32
    }

    /// Resume a suspended fiber with fresh fuel.
    ///
    /// 1. Saves host state to JitContext.
    /// 2. Restores JIT state (x29, x30, sp, scratch regs x9-x15).
    /// 3. Sets x20=ctx, x21=fuel.
    /// 4. `ret` → resumes at the saved resume point (.continue after fuel check).
    unsafe fn fiber_resume(&mut self, fuel: i64) -> u32 {
        let ctx_ptr = &mut self.ctx as *mut JitContext;
        let status: u32;

        unsafe {
            std::arch::asm!(
                // Save host state.
                "adr x0, 2f",
                "stp x29, x0, [{ctx}, #72]",   // host_fp + host_lr
                "mov x0, sp",
                "str x0, [{ctx}, #64]",         // host_sp
                "str x20, [{ctx}, #88]",        // host_ctx

                // Restore JIT state.
                "mov x20, {ctx}",
                "ldr x29, [x20, #56]",          // locals base
                "ldr x30, [x20, #32]",          // resume LR
                "ldr x0, [x20, #40]",           // jit SP
                "mov sp, x0",

                // Restore scratch registers (x9-x15).
                "ldp x9, x10, [x20, #104]",
                "ldp x11, x12, [x20, #120]",
                "ldp x13, x14, [x20, #136]",
                "ldr x15, [x20, #152]",

                // Refuel.
                "mov x21, {fuel}",

                // Resume: ret → resume_lr → .continue after fuel check.
                "ret",

                // Landing pad (same as fiber_start).
                "2:",

                ctx = in(reg) ctx_ptr,
                fuel = in(reg) fuel,
                out("x0") status,
                out("x9") _, out("x10") _,
                out("x11") _, out("x12") _,
                out("x13") _, out("x14") _,
                out("x15") _,
                out("x20") _, out("x21") _,
                out("x30") _,
            );
        }

        status
    }
}
