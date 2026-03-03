pub mod body;
mod func;
pub mod op;

use std::collections::HashMap;
use std::ops::Deref;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use wasmparser::{Parser, Payload, WasmFeatures};

use body::ParsedBody;
pub use func::{FuncIdx, FuncMeta};

static NEXT_MODULE_ID: AtomicU64 = AtomicU64::new(1);

/// Unique identifier for a parsed module.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ModuleId(u64);

impl ModuleId {
    fn next() -> Self {
        Self(NEXT_MODULE_ID.fetch_add(1, Ordering::Relaxed))
    }
}

impl Deref for ModuleId {
    type Target = u64;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// A parsed and validated WASM module with metadata for all functions.
#[derive(Debug, Clone)]
pub struct ParsedModule {
    inner: Arc<ParsedModuleInner>,
}

impl Deref for ParsedModule {
    type Target = ParsedModuleInner;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

#[derive(Debug)]
pub struct ParsedModuleInner {
    pub id: ModuleId,
    pub funcs: Vec<FuncMeta>,
    pub exports: HashMap<String, FuncIdx>,
}

impl ParsedModule {
    /// Parse and validate a WASM binary, producing a fully decoded module.
    pub fn new(bytes: &[u8]) -> Result<Self, anyhow::Error> {
        Ok(Self {
            inner: Arc::new(ParsedModuleInner::parse(bytes)?),
        })
    }

    /// Resolve an export name to a function index.
    pub fn resolve_export(&self, name: &str) -> Option<FuncIdx> {
        self.exports.get(name).cloned()
    }
}

impl ParsedModuleInner {
    fn parse(bytes: &[u8]) -> Result<Self, anyhow::Error> {
        let mut features = WasmFeatures::default();
        features.set(WasmFeatures::COMPONENT_MODEL, true);
        features.set(WasmFeatures::CM_ASYNC, true);
        features.set(WasmFeatures::CM_ASYNC_STACKFUL, true);
        features.set(WasmFeatures::CM_ASYNC_BUILTINS, true);

        let mut validator = wasmparser::Validator::new_with_features(features);
        let types = validator.validate_all(bytes)?;

        let mut builder = ModuleBuilder::new(&types, bytes);
        let parser = Parser::new(0);
        for payload in parser.parse_all(bytes) {
            builder.process_payload(payload?)?;
        }

        Ok(builder.build())
    }
}

struct ModuleBuilder<'a> {
    types: &'a wasmparser::types::Types,
    wasm_bytes: &'a [u8],
    /// (decoded_body, raw_bytes, declared_locals) per code section entry.
    bodies: Vec<(ParsedBody, Box<[u8]>, Vec<wasmparser::ValType>)>,
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

    fn process_payload(&mut self, payload: Payload) -> Result<(), anyhow::Error> {
        match payload {
            Payload::CodeSectionEntry(body) => self.parse_body(body),
            Payload::ExportSection(reader) => {
                for export in reader {
                    let export = export?;
                    if export.kind == wasmparser::ExternalKind::Func {
                        self.exports
                            .insert(export.name.to_string(), FuncIdx::new(export.index));
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

        // Extract raw operator bytes.
        let range = body.range();
        let operators_reader = body.get_operators_reader()?;
        let ops_offset = operators_reader.original_position();
        let raw_bytes = &self.wasm_bytes[ops_offset..range.end];

        // Decode into InlineOp stream.
        let types_ref = self.types.as_ref();
        let decoded = ParsedBody::parse(&body, &types_ref)?;

        self.bodies
            .push((decoded, raw_bytes.to_vec().into_boxed_slice(), body_locals));
        Ok(())
    }

    fn build(mut self) -> ParsedModuleInner {
        let types_ref = self.types.as_ref();
        let total = types_ref.function_count();
        let num_imported = total - self.bodies.len() as u32;

        let funcs = (0..total)
            .map(|idx| {
                let core_type_id = types_ref.core_function_at(idx);
                let func_type = types_ref[core_type_id].unwrap_func();
                let params = func_type.params();

                let (mut decoded, body_bytes, body_locals) = if idx < num_imported {
                    (ParsedBody::import(), Box::new([]) as Box<[u8]>, vec![])
                } else {
                    std::mem::take(&mut self.bodies[(idx - num_imported) as usize])
                };

                let results: Box<[wasmparser::ValType]> = func_type.results().into();

                // Patch function-level block (index 0) with result count.
                let rc = results.len() as u32;
                if !decoded.blocks.is_empty() {
                    decoded.blocks[0].result_count = rc;
                }

                FuncMeta {
                    params: params.into(),
                    locals: body_locals.into(),
                    results,
                    body: decoded,
                    body_bytes,
                }
            })
            .collect();

        ParsedModuleInner {
            id: ModuleId::next(),
            funcs,
            exports: self.exports,
        }
    }
}
