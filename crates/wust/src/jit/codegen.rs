use crate::Module;
use crate::jit::compiler;

use wust_codegen::disasm::{CodegenOutput, FunctionOutput};
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

    /// Run the pipeline.
    pub fn compile(self) -> Result<CodegenOutput, anyhow::Error> {
        // Reverse map: func index → export name.
        let mut names: Vec<Option<&str>> = vec![None; self.module.funcs.len()];
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

            let compiled = lower_aarch64::lower(&ir)?;
            let code = compiled.code.clone();

            functions.push((
                name,
                FunctionOutput {
                    ir: ir_text,
                    code,
                    markers: compiled.markers,
                    ir_inst_count,
                },
            ));
        }

        Ok(CodegenOutput { functions })
    }
}
