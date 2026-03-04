mod context;
mod fibre_stack;
pub(crate) mod frame;
mod wasm_stack;

use wasmparser::ValType;

use crate::module::ParsedModule;
use crate::module::body::slot_size;
use crate::task::frame::FrameHeader;
use crate::value::Val;
use crate::{FuncIdx, Instance};
pub use context::{Context, Outcome};
pub use fibre_stack::FibreStackPointer;
pub use frame::FRAME_HEADER_SIZE;
pub use wasm_stack::WasmFramePointer;

/// Independent execution context — the unit of suspension and
/// serialization. Owns its own call stack, fiber stack, and context.
pub struct Task {
    pub context: Context,
    pub module: ParsedModule,
}

impl Task {
    /// Set up a new task for calling the named export with the given args.
    pub fn setup(
        instance: &Instance,
        function_name: &str,
        args: &[Val],
    ) -> Result<Self, anyhow::Error> {
        let func_idx = instance
            .module()
            .resolve_export(function_name)
            .ok_or_else(|| anyhow::anyhow!("export '{function_name}' not found"))?;
        Self::setup_with_func_idx(instance, func_idx, args)
    }

    /// Set up a new task for calling the function at the given index.
    ///
    /// Stack layout after setup:
    /// ```text
    /// [FrameHeader][locals...]
    /// ^fp                     ^sp (stack top)
    /// ```
    pub fn setup_with_func_idx(
        instance: &Instance,
        func_idx: FuncIdx,
        args: &[Val],
    ) -> Result<Self, anyhow::Error> {
        let module = instance.module();
        let func = module
            .funcs
            .get(*func_idx as usize)
            .ok_or_else(|| anyhow::anyhow!("function {func_idx} not found"))?;

        let mut wasm_fp = WasmFramePointer::new()?;
        let fibre_sp = FibreStackPointer::new()?;
        let base = wasm_fp.base();

        unsafe {
            // Write frame header at base (outermost: prev_fp_offset=0).
            std::ptr::write(base as *mut FrameHeader, FrameHeader::new(func_idx, 0, 0));
            let locals_base = base.add(FRAME_HEADER_SIZE);
            write_locals(locals_base, func, args);
            wasm_fp.ptr = base;
        }

        Ok(Self {
            context: Context {
                outcome: Outcome::Ready,
                fuel: 0,
                wasm_fp,
                fibre_sp,
            },
            module: module.clone(),
        })
    }

    /// Reset the task for another call, reusing existing stack allocations.
    pub fn reset(&mut self, func_idx: FuncIdx, args: &[Val]) {
        let func = &self.module.funcs[*func_idx as usize];
        let base = self.context.wasm_fp.base();

        unsafe {
            std::ptr::write(base as *mut FrameHeader, FrameHeader::new(func_idx, 0, 0));
            let locals_base = base.add(FRAME_HEADER_SIZE);
            write_locals(locals_base, func, args);
            self.context.wasm_fp.ptr = base;
        }
        self.context.outcome = Outcome::Ready;
    }

    /// Read results after `Outcome::Return`.
    ///
    /// `wasm_fp.ptr` points at the outermost FrameHeader. Read func_idx,
    /// then results sit on the operand stack after locals.
    pub fn results(&self) -> Vec<Val> {
        let wasm_fp = &self.context.wasm_fp;
        let func_idx = wasm_fp.frame().func_idx();
        let func = &self.module.funcs[*func_idx as usize];
        let operand_base = unsafe {
            wasm_fp
                .ptr
                .add(FRAME_HEADER_SIZE + func.locals_size_bytes() as usize)
        };

        let mut vals = Vec::new();
        let mut offset = 0usize;
        for ty in func.results.iter() {
            vals.push(unsafe { read_compact(operand_base.add(offset), ty) });
            offset += slot_size(*ty) as usize * 4;
        }
        vals
    }
}

/// Write args into locals and zero the rest.
unsafe fn write_locals(locals_base: *mut u8, func: &crate::module::FuncMeta, args: &[Val]) {
    let total = func.locals_size_bytes() as usize;
    unsafe { std::ptr::write_bytes(locals_base, 0, total) };
    for (i, (arg, ty)) in args.iter().zip(func.params.iter()).enumerate() {
        let offset = func.local_byte_offsets[i] as usize;
        unsafe { write_compact(locals_base.add(offset), arg, ty) };
    }
}

/// Write a Val to the stack in compact format (4 bytes for i32/f32, 8 for i64/f64).
unsafe fn write_compact(dst: *mut u8, val: &Val, _ty: &ValType) {
    unsafe {
        match val {
            Val::I32(v) => (dst as *mut i32).write_unaligned(*v),
            Val::I64(v) => (dst as *mut i64).write_unaligned(*v),
            Val::F32(v) => (dst as *mut u32).write_unaligned(v.to_bits()),
            Val::F64(v) => (dst as *mut u64).write_unaligned(v.to_bits()),
            _ => todo!("write_compact for {val:?}"),
        }
    }
}

/// Read a Val from the stack in compact format.
unsafe fn read_compact(src: *const u8, ty: &ValType) -> Val {
    unsafe {
        match ty {
            ValType::I32 => Val::I32((src as *const i32).read_unaligned()),
            ValType::I64 => Val::I64((src as *const i64).read_unaligned()),
            ValType::F32 => Val::F32(f32::from_bits((src as *const u32).read_unaligned())),
            ValType::F64 => Val::F64(f64::from_bits((src as *const u64).read_unaligned())),
            _ => todo!("read_compact for {ty:?}"),
        }
    }
}
