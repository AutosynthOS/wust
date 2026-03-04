pub mod body;
mod func;
pub mod op;
mod op_display_impl;

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

/// Raw body data extracted from the code section, before full decoding.
struct RawBody {
    body_locals: Vec<wasmparser::ValType>,
    raw_bytes: Box<[u8]>,
    /// The FunctionBody range for re-reading operators during decode.
    range: std::ops::Range<usize>,
}

struct ModuleBuilder<'a> {
    types: &'a wasmparser::types::Types,
    wasm_bytes: &'a [u8],
    raw_bodies: Vec<RawBody>,
    exports: HashMap<String, FuncIdx>,
}

impl<'a> ModuleBuilder<'a> {
    fn new(types: &'a wasmparser::types::Types, wasm_bytes: &'a [u8]) -> Self {
        Self {
            types,
            wasm_bytes,
            raw_bodies: Vec::new(),
            exports: HashMap::new(),
        }
    }

    fn process_payload(&mut self, payload: Payload) -> Result<(), anyhow::Error> {
        match payload {
            Payload::CodeSectionEntry(body) => self.collect_body(body),
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

    /// Collect raw body data without full decoding — we need param types
    /// from the type section first, which are only available in build().
    fn collect_body(&mut self, body: wasmparser::FunctionBody) -> Result<(), anyhow::Error> {
        let mut body_locals = Vec::new();
        for local in body.get_locals_reader()? {
            let (count, val_type) = local?;
            for _ in 0..count {
                body_locals.push(val_type);
            }
        }

        let range = body.range();
        let operators_reader = body.get_operators_reader()?;
        let ops_offset = operators_reader.original_position();
        let raw_bytes = &self.wasm_bytes[ops_offset..range.end];

        self.raw_bodies.push(RawBody {
            body_locals,
            raw_bytes: raw_bytes.to_vec().into_boxed_slice(),
            range: range.start..range.end,
        });
        Ok(())
    }

    fn build(mut self) -> ParsedModuleInner {
        let types_ref = self.types.as_ref();
        let total = types_ref.function_count();
        let num_imported = total - self.raw_bodies.len() as u32;

        let funcs = (0..total)
            .map(|idx| {
                let core_type_id = types_ref.core_function_at(idx);
                let func_type = types_ref[core_type_id].unwrap_func();
                let params: Box<[wasmparser::ValType]> = func_type.params().into();
                let results: Box<[wasmparser::ValType]> = func_type.results().into();

                if idx < num_imported {
                    let local_byte_offsets = FuncMeta::compute_local_offsets(&params, &[]);
                    let locals_size = FuncMeta::compute_locals_size(&params, &[]);
                    return FuncMeta {
                        params,
                        locals: Box::new([]),
                        results,
                        body: ParsedBody::import(),
                        body_bytes: Box::new([]),
                        local_byte_offsets,
                        locals_size,
                    };
                }

                let raw = std::mem::replace(
                    &mut self.raw_bodies[(idx - num_imported) as usize],
                    RawBody {
                        body_locals: vec![],
                        raw_bytes: Box::new([]),
                        range: 0..0,
                    },
                );

                // All local types: params followed by declared locals.
                let all_local_types: Vec<wasmparser::ValType> = params
                    .iter()
                    .chain(raw.body_locals.iter())
                    .copied()
                    .collect();

                // Single-pass decode: parse opcodes AND compute operand depth.
                let reader = wasmparser::BinaryReader::new(
                    &self.wasm_bytes[raw.range.start..raw.range.end],
                    raw.range.start,
                );
                let body = wasmparser::FunctionBody::new(reader);
                let locals_box: Box<[wasmparser::ValType]> = raw.body_locals.into();
                let local_byte_offsets =
                    FuncMeta::compute_local_offsets(&params, &locals_box);

                let decoded = ParsedBody::parse(
                    &body, &types_ref, &all_local_types, &results, &local_byte_offsets,
                ).expect("body decode failed (already validated)");
                let locals_size = FuncMeta::compute_locals_size(&params, &locals_box);

                FuncMeta {
                    params,
                    locals: locals_box,
                    results,
                    body: decoded,
                    body_bytes: raw.raw_bytes,
                    local_byte_offsets,
                    locals_size,
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
