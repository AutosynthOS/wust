mod context;
mod fibre_stack;
pub(crate) mod frame;
mod wasm_stack;

use wasmparser::ValType;

use crate::module::ParsedModule;
use crate::task::frame::WasmFrame;
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

    /// Set up a new task for calling the function with the given args.
    pub fn setup_with_func_idx(
        instance: &Instance,
        func_idx: FuncIdx,
        args: &[Val],
    ) -> Result<Self, anyhow::Error> {
        instance
            .module()
            .funcs
            .get(*func_idx as usize)
            .ok_or_else(|| anyhow::anyhow!("function {func_idx} not found"))?;

        let wasm_fp = WasmFramePointer::new(WasmFrame::from(func_idx, 0))?;
        let fibre_sp = FibreStackPointer::new()?;

        for (i, arg) in args.iter().enumerate() {
            wasm_fp.write_local(i * 8, arg.to_raw());
        }

        Ok(Self {
            context: Context {
                outcome: Outcome::Ready,
                fuel: 0,
                wasm_fp,
                fibre_sp,
            },
            module: instance.module().clone(),
        })
    }

    /// Read results from the frame after `Outcome::Return`.
    pub fn results(&self) -> Vec<Val> {
        let wasm_fp = &self.context.wasm_fp;
        let func_idx = wasm_fp.frame().func_idx();
        let func = &self.module.funcs[*func_idx as usize];
        func.results
            .iter()
            .enumerate()
            .map(|(i, ty)| {
                let raw = wasm_fp.read_local(i * 8);
                read_typed(raw, ty)
            })
            .collect()
    }
}

fn read_typed(raw: u64, ty: &ValType) -> Val {
    match ty {
        ValType::I32 => Val::I32(raw as i32),
        ValType::I64 => Val::I64(raw as i64),
        ValType::F32 => Val::F32(f32::from_bits(raw as u32)),
        ValType::F64 => Val::F64(f64::from_bits(raw)),
        _ => todo!("return type {ty:?} not yet supported"),
    }
}
