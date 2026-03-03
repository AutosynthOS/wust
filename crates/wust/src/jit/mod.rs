pub mod codegen;
pub(crate) mod compiler;
#[cfg(test)]
pub(crate) mod tests;

use wust_core::{Outcome, ParsedModule, Task};

use crate::exec::ModuleExecutor;

use wust_codegen::code_buffer::CodeBuffer;
use wust_codegen::emit::{self, Emitter};
use wust_codegen::ir::IrFunction;
use wust_codegen::lower_aarch64;
use wust_codegen::lower_aarch64::SharedHandlerOffsets;

/// Per-function snapshot passed to the `compile_all` callback.
pub(crate) struct FuncSnapshot {
    /// Word offset where the function's code starts in the emitter.
    pub(crate) code_start: usize,
    /// Index into the markers array where this function's markers start.
    pub(crate) markers_start: usize,
    /// Label index → word offset relative to function start.
    pub(crate) label_offsets: Vec<Option<usize>>,
}

/// Compile all functions in a module into a shared emitter.
///
/// Emits the shared preamble (jump table, handlers), then compiles
/// each function's IR and lowers it to machine code. Calls `on_func`
/// after each function is lowered with the IR and pre/post snapshot.
pub(crate) fn compile_all(
    module: &ParsedModule,
    emit_fuel: bool,
    emit_markers: bool,
    mut on_func: impl FnMut(usize, &IrFunction, &Emitter, &FuncSnapshot),
) -> (Emitter, SharedHandlerOffsets, Vec<usize>) {
    let func_count = module.funcs.len();
    let mut e = emit::Emitter::new();
    let shared = lower_aarch64::emit_shared_preamble(&mut e, func_count);
    let mut body_offsets: Vec<Option<usize>> = vec![None; func_count];
    let mut func_body_starts: Vec<usize> = Vec::with_capacity(func_count);

    for (i, func) in module.funcs.iter().enumerate() {
        let ir = compiler::compile_with(func, &module.funcs, emit_fuel);
        let code_start = e.code().len();
        let markers_start = e.markers().len();
        let result =
            lower_aarch64::lower_into(&mut e, &ir, i as u32, &mut body_offsets, emit_markers);
        lower_aarch64::patch_jump_table(&mut e, i as u32, result.body_start);
        func_body_starts.push(result.body_start);
        let snap = FuncSnapshot {
            code_start,
            markers_start,
            label_offsets: result.label_offsets,
        };
        on_func(i, &ir, &e, &snap);
    }

    // Emit per-function entry trampolines (host→JIT entry points).
    let entry_trampolines: Vec<usize> = (0..func_count)
        .map(|i| {
            let func = &module.funcs[i];
            lower_aarch64::emit_entry_trampoline(
                &mut e,
                func_body_starts[i],
                func.param_count(),
                func.results.len(),
            )
        })
        .collect();

    (e, shared, entry_trampolines)
}

/// A JIT-compiled module with a shared code buffer.
///
/// All functions live in a single mmap'd region. A jump table at the
/// start dispatches calls via PC-relative branches — no indirect
/// loads, no runtime function table.
pub struct JitModule {
    /// Single code buffer containing all compiled code.
    buffer: CodeBuffer,
    /// Per-function entry trampoline word offsets.
    entry_trampolines: Vec<usize>,
    // TODO: store ModuleId once Module wraps ModuleMeta
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
    module: &'a ParsedModule,
    emit_fuel: bool,
}

impl<'a> JitCompiler<'a> {
    pub fn new(module: &'a ParsedModule) -> Self {
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
        let (e, _shared, entry_trampolines) =
            compile_all(self.module, self.emit_fuel, false, |_, _, _, _| {});

        let mut buffer = CodeBuffer::new(e.code().len() * 4 + 64)?;
        for &word in e.code() {
            buffer.emit_u32(word);
        }
        buffer.finalize()?;

        Ok(JitModule {
            buffer,
            entry_trampolines,
        })
    }
}

impl JitModule {
    /// Compile all functions in a module with default settings (fuel enabled).
    ///
    /// Pipeline: wasm ops → IR (virtual registers) → aarch64 machine code.
    pub fn compile(module: &ParsedModule) -> Result<Self, anyhow::Error> {
        JitCompiler::new(module).compile()
    }

    /// Low-level trampoline call.
    ///
    /// Swaps the native stack pointer to the fiber stack on entry so
    /// that JIT function prologues (`str x30, [sp, #-16]!`) save
    /// return addresses on the fiber stack — not the host stack.
    ///
    /// Returns `Outcome::Return` if the function completed normally,
    /// or `Outcome::Suspended` if fuel was exhausted.
    fn call_trampoline(&self, task: &mut Task, func_idx: usize) -> Outcome {
        const FUEL: usize = std::mem::offset_of!(wust_core::Context, fuel);
        const WASM_FP: usize = std::mem::offset_of!(wust_core::Context, wasm_fp);
        const FIBRE_SP: usize = std::mem::offset_of!(wust_core::Context, fibre_sp);

        let trampoline_offset = self.entry_trampolines[func_idx];
        let trampoline_ptr = unsafe { self.buffer.entry().add(trampoline_offset * 4) };
        let ctx = &mut task.context;

        ctx.outcome = Outcome::Running;
        let ctx_ptr = ctx as *mut wust_core::Context as u64;

        unsafe {
            std::arch::asm!(
                // Save host callee-saved regs on host stack.
                "stp x29, x30, [sp, #-16]!",
                "stp x20, x21, [sp, #-16]!",
                "stp x28, xzr, [sp, #-16]!",
                // Load JIT state from context.
                "mov x20, {ctx}",
                "ldr x21, [x20, #{fuel}]",
                "ldr x29, [x20, #{wasm_fp}]",
                "ldr x9,  [x20, #{fibre_sp}]",
                // Save host SP, switch to fiber stack.
                "mov x28, sp",
                "mov sp, x9",
                // Call the per-function trampoline.
                "blr {code}",
                // Store JIT state back to context.
                "str x21, [x20, #{fuel}]",
                "str x29, [x20, #{wasm_fp}]",
                // Restore host SP from x28.
                "mov sp, x28",
                // Restore host callee-saved regs.
                "ldp x28, xzr, [sp], #16",
                "ldp x20, x21, [sp], #16",
                "ldp x29, x30, [sp], #16",
                ctx = in(reg) ctx_ptr,
                code = in(reg) trampoline_ptr,
                fuel = const FUEL,
                wasm_fp = const WASM_FP,
                fibre_sp = const FIBRE_SP,
                out("x9") _, out("x10") _, out("x11") _,
                out("x12") _, out("x13") _, out("x14") _,
                out("x15") _, out("x28") _,
            );
        }

        // On normal return, the JIT doesn't write to ctx.outcome —
        // it stays Running. The cold stub sets it to Suspended.
        match task.context.outcome {
            Outcome::Running => Outcome::Return,
            other => other,
        }
    }
}

impl ModuleExecutor for JitModule {
    fn poll(&self, task: &mut Task) -> Outcome {
        let func_idx = *task.context.wasm_fp.frame().func_idx() as usize;
        self.call_trampoline(task, func_idx)
    }
}
