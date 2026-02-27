pub(crate) mod body;
pub(crate) mod func;

use std::collections::HashMap;

use crate::Engine;
use body::ParsedBody;
use func::FuncIdx;
use func::ParsedFunction;
use wasmparser::Export;
use wasmparser::ExportSectionReader;
use wasmparser::FunctionBody;
use wasmparser::ValType;
use wasmparser::types::Types;
use wasmparser::{Parser, Payload};

pub(crate) struct ParsedModule {
    pub(crate) funcs: Vec<ParsedFunction>,
    pub(crate) exports: HashMap<String, FuncIdx>,
}

pub(crate) fn parse(engine: &Engine, bytes: &[u8]) -> Result<ParsedModule, anyhow::Error> {
    let mut validator = engine.new_validator();
    let types = validator.validate_all(bytes)?;

    let mut builder = ModuleBuilder::default();
    let parser = Parser::new(0);
    for payload in parser.parse_all(bytes) {
        builder.process_payload(payload?)?;
    }

    Ok(builder.build(types))
}

#[derive(Default)]
struct ModuleBuilder {
    /// Parsed function bodies with their declared locals.
    bodies: Vec<(ParsedBody, Vec<ValType>)>,
    /// Function exports: name → function index.
    exports: HashMap<String, FuncIdx>,
}

impl ModuleBuilder {
    fn process_payload(&mut self, payload: Payload) -> Result<(), anyhow::Error> {
        match payload {
            Payload::CodeSectionEntry(body) => self.parse_body(body),
            Payload::ExportSection(reader) => self.parse_export_section(reader),
            _ => Ok(()),
        }
    }

    fn parse_export_section(&mut self, reader: ExportSectionReader) -> Result<(), anyhow::Error> {
        for export in reader {
            self.parse_export(export?)?;
        }
        Ok(())
    }

    fn parse_export(&mut self, export: Export) -> Result<(), anyhow::Error> {
        if export.kind == wasmparser::ExternalKind::Func {
            self.exports
                .insert(export.name.to_string(), FuncIdx(export.index));
        }
        Ok(())
    }

    fn parse_body(&mut self, body: FunctionBody) -> Result<(), anyhow::Error> {
        let mut body_locals = Vec::new();
        for local in body.get_locals_reader()? {
            let (count, val_type) = local?;
            for _ in 0..count {
                body_locals.push(val_type);
            }
        }
        let parsed = ParsedBody::parse(&body)?;
        self.bodies.push((parsed, body_locals));
        Ok(())
    }

    fn build(mut self, types: Types) -> ParsedModule {
        let total = types.as_ref().function_count();
        let num_imported = total - self.bodies.len() as u32;
        let types_ref = types.as_ref();

        let funcs = (0..total)
            .map(|idx| {
                let core_type_id = types_ref.core_function_at(idx);
                let func_type = types_ref[core_type_id].unwrap_func();
                let params = func_type.params();
                let param_count = params.len();

                let (body, body_locals) = if idx < num_imported {
                    (ParsedBody::empty(), vec![])
                } else {
                    // Take to avoid cloning.
                    std::mem::take(&mut self.bodies[(idx - num_imported) as usize])
                };

                // locals = params ++ body-declared locals
                let mut locals: Vec<ValType> = params.into();
                locals.extend(body_locals);

                let results: Box<[ValType]> = func_type.results().into();
                let local_count = locals.len();
                ParsedFunction {
                    result_count: results.len() as u32,
                    arg_byte_count: param_count * 8,
                    extra_local_bytes: (local_count - param_count) * 8,
                    locals: locals.into(),
                    results,
                    param_count,
                    body,
                }
            })
            .collect();

        ParsedModule {
            funcs,
            exports: self.exports,
        }
    }
}
