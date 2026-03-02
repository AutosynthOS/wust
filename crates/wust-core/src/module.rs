use std::collections::HashMap;

use wasmparser::{ValType, WasmFeatures};

/// Index into the module's function list.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FuncIdx(pub u32);

/// Metadata for a single function in a module.
#[derive(Debug, Clone)]
pub struct FuncMeta {
    /// All locals: params first, then body-declared locals.
    pub locals: Box<[ValType]>,
    /// Result types.
    pub results: Box<[ValType]>,
    /// Number of parameters (first N entries in `locals`).
    pub param_count: usize,
    /// Raw WASM bytecode for the function body (code section bytes).
    /// Empty for imported functions.
    pub body_bytes: Box<[u8]>,
    /// Precomputed: `param_count * 8` (byte size of args on stack).
    pub arg_byte_count: usize,
    /// Precomputed: `(locals.len() - param_count) * 8` (bytes to zero).
    pub extra_local_bytes: usize,
    /// Precomputed: number of result values.
    pub result_count: u32,
}

impl FuncMeta {
    pub fn param_count(&self) -> usize {
        self.param_count
    }
}

/// A parsed and validated WASM module with metadata for all functions.
#[derive(Debug, Clone)]
pub struct ModuleMeta {
    pub funcs: Vec<FuncMeta>,
    pub exports: HashMap<String, FuncIdx>,
}

/// Parse and validate a WASM binary, producing module metadata.
///
/// This performs full validation via `wasmparser` and extracts function
/// signatures, locals, exports, and raw body bytes. No IR conversion
/// happens here — engines are responsible for lowering the raw bytes
/// into their own instruction formats.
pub fn parse(bytes: &[u8]) -> Result<ModuleMeta, anyhow::Error> {
    let mut features = WasmFeatures::default();
    features.set(WasmFeatures::COMPONENT_MODEL, true);
    features.set(WasmFeatures::CM_ASYNC, true);
    features.set(WasmFeatures::CM_ASYNC_STACKFUL, true);
    features.set(WasmFeatures::CM_ASYNC_BUILTINS, true);

    let mut validator = wasmparser::Validator::new_with_features(features);
    let types = validator.validate_all(bytes)?;

    let mut builder = ModuleBuilder::new(&types, bytes);
    let parser = wasmparser::Parser::new(0);
    for payload in parser.parse_all(bytes) {
        builder.process_payload(payload?)?;
    }

    Ok(builder.build())
}

struct ModuleBuilder<'a> {
    types: &'a wasmparser::types::Types,
    wasm_bytes: &'a [u8],
    /// (body_bytes, declared_locals) for each code section entry.
    bodies: Vec<(Box<[u8]>, Vec<ValType>)>,
    exports: HashMap<String, FuncIdx>,
}

impl<'a> ModuleBuilder<'a> {
    fn new(types: &'a wasmparser::types::Types, wasm_bytes: &'a [u8]) -> Self {
        Self {
            types,
            wasm_bytes,
            bodies: Vec::new(),
            exports: HashMap::new(),
        }
    }

    fn process_payload(&mut self, payload: wasmparser::Payload) -> Result<(), anyhow::Error> {
        match payload {
            wasmparser::Payload::CodeSectionEntry(body) => self.parse_body(body),
            wasmparser::Payload::ExportSection(reader) => {
                for export in reader {
                    let export = export?;
                    if export.kind == wasmparser::ExternalKind::Func {
                        self.exports
                            .insert(export.name.to_string(), FuncIdx(export.index));
                    }
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn parse_body(&mut self, body: wasmparser::FunctionBody) -> Result<(), anyhow::Error> {
        let mut body_locals = Vec::new();
        for local in body.get_locals_reader()? {
            let (count, val_type) = local?;
            for _ in 0..count {
                body_locals.push(val_type);
            }
        }

        // Store the raw operator bytes. The range covers the full body;
        // we slice from the operators reader offset to get past locals.
        let range = body.range();
        let operators_reader = body.get_operators_reader()?;
        let ops_offset = operators_reader.original_position();
        let raw_bytes = &self.wasm_bytes[ops_offset..range.end];

        self.bodies
            .push((raw_bytes.to_vec().into_boxed_slice(), body_locals));
        Ok(())
    }

    fn build(mut self) -> ModuleMeta {
        let types_ref = self.types.as_ref();
        let total = types_ref.function_count();
        let num_imported = total - self.bodies.len() as u32;

        let funcs = (0..total)
            .map(|idx| {
                let core_type_id = types_ref.core_function_at(idx);
                let func_type = types_ref[core_type_id].unwrap_func();
                let params = func_type.params();
                let param_count = params.len();

                let (body_bytes, body_locals) = if idx < num_imported {
                    (Box::new([]) as Box<[u8]>, vec![])
                } else {
                    std::mem::take(&mut self.bodies[(idx - num_imported) as usize])
                };

                let mut locals: Vec<ValType> = params.into();
                locals.extend(body_locals);

                let results: Box<[ValType]> = func_type.results().into();
                let local_count = locals.len();

                FuncMeta {
                    result_count: results.len() as u32,
                    arg_byte_count: param_count * 8,
                    extra_local_bytes: (local_count - param_count) * 8,
                    locals: locals.into(),
                    results,
                    param_count,
                    body_bytes,
                }
            })
            .collect();

        ModuleMeta {
            funcs,
            exports: self.exports,
        }
    }
}
