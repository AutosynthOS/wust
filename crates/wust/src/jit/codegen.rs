use wasmparser::ValType;

use wust_core::{FuncMeta, ParsedModule};
use crate::jit::compile_all;

use wust_codegen::disasm::{Block, BlockAnnotations, CodegenOutput};

fn valtype_str(ty: &ValType) -> &'static str {
    match ty {
        ValType::I32 => "i32",
        ValType::I64 => "i64",
        ValType::F32 => "f32",
        ValType::F64 => "f64",
        ValType::V128 => "v128",
        ValType::Ref(_) => "ref",
    }
}

/// Build a short name like `answer<1>` or `<0>`.
fn func_name(export_name: Option<&str>, idx: usize) -> String {
    match export_name {
        Some(name) => format!("{name}<{idx}>"),
        None => format!("<{idx}>"),
    }
}

/// Build a full signature like `answer<1>(x9: i32) -> x9: i32`.
/// Register prefix for a ValType: `w` for 32-bit, `x` for 64-bit.
fn reg_prefix(ty: &ValType) -> &'static str {
    match ty {
        ValType::I32 | ValType::F32 => "w",
        _ => "x",
    }
}

fn func_signature(func: &FuncMeta, export_name: Option<&str>, idx: usize) -> String {
    let name = func_name(export_name, idx);
    let params: Vec<String> = func.params
        .iter()
        .enumerate()
        .map(|(i, ty)| format!("{}{}<{}>", reg_prefix(ty), 9 + i, valtype_str(ty)))
        .collect();
    let results: Vec<String> = func.results
        .iter()
        .enumerate()
        .map(|(i, ty)| format!("{}{}<{}>", reg_prefix(ty), 9 + i, valtype_str(ty)))
        .collect();
    let result_part = match results.len() {
        0 => String::new(),
        1 => format!(" -> {}", results[0]),
        _ => format!(" -> ({})", results.join(", ")),
    };
    format!("{name}({}){result_part}", params.join(", "))
}

/// Builder for the codegen pipeline.
pub struct Codegen<'a> {
    module: &'a ParsedModule,
    emit_fuel: bool,
}

impl<'a> Codegen<'a> {
    pub fn new(module: &'a ParsedModule) -> Self {
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

    /// Run the pipeline, producing a unified view of all emitted code.
    pub fn compile(self) -> Result<CodegenOutput, anyhow::Error> {
        let func_count = self.module.funcs.len();

        // Reverse map: func index → export name.
        let mut export_names: Vec<Option<&str>> = vec![None; func_count];
        for (name, idx) in &self.module.exports {
            let i = **idx as usize;
            if i < export_names.len() {
                export_names[i] = Some(name.as_str());
            }
        }

        // Build full signatures for each function.
        let signatures: Vec<String> = (0..func_count)
            .map(|i| func_signature(&self.module.funcs[i], export_names[i], i))
            .collect();

        let mut blocks: Vec<Block> = Vec::new();
        let mut func_body_starts: Vec<usize> = Vec::new();

        let module = self.module;
        let (e, shared, trampolines) = compile_all(
            module,
            self.emit_fuel,
            true,
            |i, ir, emitter, snap| {
                func_body_starts.push(snap.code_start);

                let code = emitter.code()[snap.code_start..].to_vec();
                let markers: Vec<usize> = emitter.markers()[snap.markers_start..]
                    .iter()
                    .map(|m| m - snap.code_start)
                    .collect();
                let fused = crate::jit::fuse::fuse(&module.funcs[i].body);
                let op_labels: Vec<String> = fused.ops.iter()
                    .map(|op| {
                        crate::jit::fuse::display_label(*op)
                            .unwrap_or_else(|| op.display_label())
                    })
                    .collect();

                // Filter source_ops to only include entries for
                // marker-producing IR instructions (skip DefLabel,
                // FuelConsume, FuelCheck — their code merges into
                // surrounding regions).
                use wust_codegen::ir::IrInst;
                let filtered_source_ops: Vec<u32> = ir.insts.iter()
                    .zip(ir.source_ops.iter())
                    .filter(|(inst, _)| !matches!(inst,
                        IrInst::DefLabel { .. } |
                        IrInst::FuelConsume { .. } |
                        IrInst::FuelCheck { .. }
                    ))
                    .map(|(_, &op)| op)
                    .collect();

                blocks.push(Block {
                    name: signatures[i].clone(),
                    code,
                    base_offset: snap.code_start * 4,
                    annotations: Some(BlockAnnotations {
                        markers,
                        ir_inst_count: filtered_source_ops.len(),
                        source_ops: filtered_source_ops,
                        op_labels,
                        label_offsets: snap.label_offsets.clone(),
                        param_types: module.funcs[i].params.iter().map(valtype_str).collect(),
                        result_types: module.funcs[i].results.iter().map(valtype_str).collect(),
                        word_labels: snap.word_labels.clone(),
                    }),
                });
            },
        );

        let full_code = e.code();

        // Build all blocks: shared handlers first, then trampolines,
        // then function bodies (already collected above).
        let mut all_blocks: Vec<Block> = Vec::new();

        // Jump table (shared preamble).
        if shared.end > 0 {
            all_blocks.push(Block {
                name: "jump table (unused)".into(),
                code: full_code[..shared.end].to_vec(),
                base_offset: 0,
                annotations: None,
            });
        }

        // Per-function entry trampolines.
        for (i, &tramp_offset) in trampolines.iter().enumerate() {
            let tramp_end = trampolines.get(i + 1).copied().unwrap_or(full_code.len());
            let short_name = func_name(export_names[i], i);
            all_blocks.push(Block {
                name: format!("trampoline:{short_name}(frame_base: x0<u64>, fuel: x1<i64>)"),
                code: full_code[tramp_offset..tramp_end].to_vec(),
                base_offset: tramp_offset * 4,
                annotations: None,
            });
        }

        // Function bodies.
        all_blocks.append(&mut blocks);

        // Global label map — derived from block names/offsets.
        let labels: Vec<(usize, String)> = all_blocks
            .iter()
            .map(|b| (b.base_offset, b.name.clone()))
            .collect();

        Ok(CodegenOutput {
            blocks: all_blocks,
            labels,
        })
    }
}
