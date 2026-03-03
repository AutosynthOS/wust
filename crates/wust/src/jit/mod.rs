pub mod codegen;
pub(crate) mod compiler;
#[cfg(test)]
pub(crate) mod tests;

use wasmparser::ValType;

use crate::Module;
use crate::value::Val;

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
    module: &Module,
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
    pub fn compile(module: &Module) -> Result<Self, anyhow::Error> {
        JitCompiler::new(module).compile()
    }

    /// Call an exported function by name, returning results as `Vec<Val>`.
    ///
    /// Writes args into the wasm frame, calls the entry trampoline,
    /// and reads results back using the function's type signature.
    pub fn call_dynamic(
        &self,
        module: &Module,
        instance: &mut wust_core::Instance,
        name: &str,
        args: &[Val],
    ) -> Result<Vec<Val>, anyhow::Error> {
        let func_idx = module
            .resolve_export(name)
            .ok_or_else(|| anyhow::anyhow!("export '{name}' not found"))?
            as usize;
        let func = module
            .funcs
            .get(func_idx)
            .ok_or_else(|| anyhow::anyhow!("function {func_idx} not found"))?;

        // Write args into frame slots (after the 16-byte header).
        instance.stack.set_sp(0);
        instance.stack.write_u64_at(0, 0); // zero frame header
        instance.stack.write_u64_at(8, 0);
        for (i, arg) in args.iter().enumerate() {
            instance.stack.write_u64_at(FRAME_HEADER_SIZE + i * 8, arg.to_raw());
        }

        self.call_trampoline(instance, func_idx, i64::MAX);

        // Read results from frame slots using the function's result types.
        let results = func
            .results
            .iter()
            .enumerate()
            .map(|(i, ty)| {
                let raw = instance.stack.read_u64_at(FRAME_HEADER_SIZE + i * 8);
                read_typed(raw, ty)
            })
            .collect();

        Ok(results)
    }

    /// Low-level trampoline call.
    ///
    /// Swaps the native stack pointer to the fiber stack on entry so
    /// that JIT function prologues (`str x30, [sp, #-16]!`) save
    /// return addresses on the fiber stack — not the host stack.
    fn call_trampoline(&self, instance: &wust_core::Instance, func_idx: usize, fuel: i64) {
        let trampoline_offset = self.entry_trampolines[func_idx];
        let trampoline_ptr = unsafe { self.buffer.entry().add(trampoline_offset * 4) };
        let frame_base = instance.stack.base() as u64;
        let fibre_top = instance.fibre.top() as u64;

        unsafe {
            std::arch::asm!(
                // Save host callee-saved regs on host stack.
                "stp x29, x30, [sp, #-16]!",
                "stp x20, x21, [sp, #-16]!",
                "stp x28, xzr, [sp, #-16]!",
                // Save host SP, switch to fiber stack.
                "mov x28, sp",
                "mov sp, {fibre_top}",
                // Set up JIT pinned registers.
                "mov x29, {frame_base}",     // g.fp = frame base
                "mov x21, {fuel}",           // g.fuel = fuel
                // Call the per-function trampoline.
                "blr {code}",
                // Restore host SP from x28.
                "mov sp, x28",
                // Restore host callee-saved regs.
                "ldp x28, xzr, [sp], #16",
                "ldp x20, x21, [sp], #16",
                "ldp x29, x30, [sp], #16",
                frame_base = in(reg) frame_base,
                fuel = in(reg) fuel as u64,
                fibre_top = in(reg) fibre_top,
                code = in(reg) trampoline_ptr,
                out("x9") _, out("x10") _, out("x11") _,
                out("x12") _, out("x13") _, out("x14") _,
                out("x15") _, out("x28") _,
                clobber_abi("C"),
            );
        }
    }
}

/// Frame header size in bytes (2 slots: prev_fp + header word).
const FRAME_HEADER_SIZE: usize = 16;

/// Interpret raw u64 bits as a typed `Val` based on the function's
/// result type signature.
fn read_typed(raw: u64, ty: &ValType) -> Val {
    match ty {
        ValType::I32 => Val::I32(raw as i32),
        ValType::I64 => Val::I64(raw as i64),
        ValType::F32 => Val::F32(f32::from_bits(raw as u32)),
        ValType::F64 => Val::F64(f64::from_bits(raw)),
        _ => todo!("JIT return type {ty:?} not yet supported"),
    }
}
