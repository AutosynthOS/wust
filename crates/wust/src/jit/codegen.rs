use crate::Module;
use crate::jit::compiler;

use wust_codegen::disasm::{CodegenOutput, FunctionOutput};
use wust_codegen::emit;
use wust_codegen::lower_aarch64;

/// Builder for the codegen pipeline.
pub struct Codegen<'a> {
    module: &'a Module,
    inspect: bool,
    emit_fuel: bool,
}

impl<'a> Codegen<'a> {
    pub fn new(module: &'a Module) -> Self {
        Codegen {
            module,
            inspect: false,
            emit_fuel: true,
        }
    }

    /// Enable inspection output (IR + annotated asm).
    pub fn inspect(mut self) -> Self {
        self.inspect = true;
        self
    }

    /// Enable or disable fuel check emission.
    pub fn fuel(mut self, enabled: bool) -> Self {
        self.emit_fuel = enabled;
        self
    }

    /// Run the pipeline, producing the same shared-buffer code that
    /// the real JIT uses (with PC-relative calls and direct BL).
    pub fn compile(self) -> Result<CodegenOutput, anyhow::Error> {
        let func_count = self.module.funcs.len();
        let mut e = emit::Emitter::new();

        // Emit shared preamble: jump table, interpret stubs, handlers.
        let shared = lower_aarch64::emit_shared_preamble(&mut e, func_count);

        // Track body offsets for direct BL optimization.
        let mut body_offsets: Vec<Option<usize>> = vec![None; func_count];

        // Reverse map: func index → export name.
        let mut names: Vec<Option<&str>> = vec![None; func_count];
        for (name, idx) in &self.module.exports {
            let i = idx.0 as usize;
            if i < names.len() {
                names[i] = Some(name.as_str());
            }
        }

        let mut functions = Vec::new();

        for (i, func) in self.module.funcs.iter().enumerate() {
            let name = names[i].unwrap_or("<anon>").to_string();
            let ir = compiler::compile_with(func, &self.module.funcs, self.emit_fuel);

            let ir_text = format!("{ir}");
            let ir_inst_count = ir.insts.len();

            // Snapshot state before lowering this function.
            let code_start = e.code().len();
            let markers_start = e.markers.len();

            let layout =
                lower_aarch64::lower_into(&mut e, &ir, i as u32, &shared, &mut body_offsets, true);
            let body_word = layout.body_offset / 4;
            lower_aarch64::patch_jump_table(&mut e, i as u32, body_word);

            // Extract this function's code and markers (relative to its start).
            let code = e.code()[code_start..].to_vec();
            let markers: Vec<usize> = e.markers[markers_start..]
                .iter()
                .map(|m| m - code_start)
                .collect();

            functions.push((
                name,
                FunctionOutput {
                    ir: ir_text,
                    code,
                    markers,
                    ir_inst_count,
                },
            ));
        }

        Ok(CodegenOutput { functions })
    }
}
