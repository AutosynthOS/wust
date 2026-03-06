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
    pub func_idx: FuncIdx,
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

    pub fn setup_with_func_idx(
        instance: &Instance,
        func_idx: FuncIdx,
        args: &[Val],
    ) -> Result<Self, anyhow::Error> {
        let module = instance.module();

        let mut task = Self {
            func_idx,
            context: Context {
                outcome: Outcome::Ready,
                fuel: 0,
                wasm_fp: WasmFramePointer::new()?,
                fibre_sp: FibreStackPointer::new()?,
            },
            module: module.clone(),
        };

        task.setup_root_call_frame(args)?;

        Ok(task)
    }
    /// Set up a new task for calling the function at the given index.
    ///
    /// Stack layout after setup:
    /// ```text
    /// [locals][header][... operands ... ]
    /// ^locals base    ^operand base     ^stack pointer
    /// ```
    pub fn setup_root_call_frame(&mut self, args: &[Val]) -> Result<(), anyhow::Error> {
        let func = self
            .module
            .funcs
            .get(*self.func_idx as usize)
            .ok_or_else(|| anyhow::anyhow!("function {} not found", self.func_idx))?;
        let base = self.context.wasm_fp.base();
        unsafe {
            // Layout: [locals][header] → fp points after header (= operand base).
            let locals_base = base;
            write_locals(locals_base, func, args);
            let header_ptr = base.add(func.locals_size as usize);
            std::ptr::write(
                header_ptr as *mut FrameHeader,
                FrameHeader::new(
                    self.func_idx,
                    0,
                    FRAME_HEADER_SIZE as u32 + func.locals_size as u32,
                ),
            );
            self.context.wasm_fp.ptr = header_ptr.add(FRAME_HEADER_SIZE);
        }

        Ok(())
    }

    /// Read results after `Outcome::Return`.
    ///
    /// `wasm_fp.ptr` points at the outermost FrameHeader. Read func_idx,
    /// then results sit on the operand stack after locals.
    pub fn results(&self) -> Vec<Val> {
        let func = &self.module.funcs[*self.func_idx as usize];
        let mut vals = Vec::new();
        let mut offset = 0usize;
        for ty in func.results.iter() {
            vals.push(unsafe { read_compact(self.context.wasm_fp.ptr.add(offset), ty) });
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
