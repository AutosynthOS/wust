use crate::Module;
use crate::jit::compile_all;

use wust_codegen::disasm::{CodegenOutput, FunctionOutput};

/// Builder for the codegen pipeline.
pub struct Codegen<'a> {
    module: &'a Module,
    emit_fuel: bool,
}

impl<'a> Codegen<'a> {
    pub fn new(module: &'a Module) -> Self {
        Codegen {
            module,
            emit_fuel: true,
        }
    }

    /// Enable or disable fuel check emission.
    pub fn fuel(mut self, enabled: bool) -> Self {
        self.emit_fuel = enabled;
        self
    }

    /// Run the pipeline, producing the same shared-buffer code that
    /// the real JIT uses (with PC-relative calls and direct BL).
    pub fn compile(self) -> Result<CodegenOutput, anyhow::Error> {
        // Reverse map: func index → export name.
        let func_count = self.module.funcs.len();
        let mut names: Vec<Option<&str>> = vec![None; func_count];
        for (name, idx) in &self.module.exports {
            let i = idx.0 as usize;
            if i < names.len() {
                names[i] = Some(name.as_str());
            }
        }

        let mut functions = Vec::new();

        let module = self.module;
        let (_e, _shared) = compile_all(
            module,
            self.emit_fuel,
            true,
            |i, ir, e, snap| {
                let name = names[i].unwrap_or("<anon>").to_string();
                let ir_text = format!("{ir}");
                let ir_inst_count = ir.insts.len();

                let code = e.code()[snap.code_start..].to_vec();
                let markers: Vec<usize> = e.markers()[snap.markers_start..]
                    .iter()
                    .map(|m| m - snap.code_start)
                    .collect();

                let source_ops = ir.source_ops.clone();

                let op_labels: Vec<String> = module.funcs[i]
                    .body
                    .ops
                    .iter()
                    .map(|op| op.display_label())
                    .collect();

                functions.push((
                    name,
                    FunctionOutput {
                        ir: ir_text,
                        code,
                        markers,
                        ir_inst_count,
                        source_ops,
                        op_labels,
                        label_offsets: snap.label_offsets.clone(),
                        param_count: ir.param_count as usize,
                        result_count: ir.result_count as usize,
                    },
                ));
            },
        );

        Ok(CodegenOutput { functions })
    }
}
