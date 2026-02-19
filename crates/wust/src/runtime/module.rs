use wasmparser::{
    FuncType, Operator, Parser, Payload, ValType,
};

use crate::runtime::opcode::{Op, compile_body};

/// Small instruction enum used only for const expressions (global inits,
/// data segment offsets, table inits, element items). These only need a
/// handful of variants — far fewer than the full instruction set.
#[derive(Debug, Clone)]
pub enum ConstOp {
    I32Const(i32),
    I64Const(i64),
    F32Const(f32),
    F64Const(f64),
    RefFunc(u32),
    RefNull,
    GlobalGet(u32),
    I32Add,
    I32Sub,
    I32Mul,
    I64Add,
    I64Sub,
    I64Mul,
}

/// Decode a single wasmparser operator into a ConstOp, if it is valid in
/// a const expression context. Returns None for unsupported operators.
fn decode_const_op(op: &Operator) -> Option<ConstOp> {
    Some(match *op {
        Operator::I32Const { value } => ConstOp::I32Const(value),
        Operator::I64Const { value } => ConstOp::I64Const(value),
        Operator::F32Const { value } => ConstOp::F32Const(f32::from_bits(value.bits())),
        Operator::F64Const { value } => ConstOp::F64Const(f64::from_bits(value.bits())),
        Operator::RefFunc { function_index } => ConstOp::RefFunc(function_index),
        Operator::RefNull { .. } => ConstOp::RefNull,
        Operator::GlobalGet { global_index } => ConstOp::GlobalGet(global_index),
        Operator::I32Add => ConstOp::I32Add,
        Operator::I32Sub => ConstOp::I32Sub,
        Operator::I32Mul => ConstOp::I32Mul,
        Operator::I64Add => ConstOp::I64Add,
        Operator::I64Sub => ConstOp::I64Sub,
        Operator::I64Mul => ConstOp::I64Mul,
        _ => return None,
    })
}

/// A parsed WASM module — types, functions, memory, etc.
/// This is the immutable "code" side. Instance state lives in Store.
#[derive(Debug)]
pub struct Module {
    pub types: Vec<FuncType>,
    pub funcs: Vec<Func>,
    pub memories: Vec<MemoryType>,
    pub globals: Vec<GlobalDef>,
    pub exports: Vec<Export>,
    pub data_segments: Vec<DataSegment>,
    pub tables: Vec<TableDef>,
    pub elements: Vec<ElemSegment>,
    pub start: Option<u32>,
    /// func_types[i] = index into self.types for function i
    /// (includes imports — imports come first)
    pub func_types: Vec<u32>,
    /// Import counts — imported items come first in the index space.
    pub num_func_imports: u32,
    pub num_global_imports: u32,
    pub num_memory_imports: u32,
    pub num_table_imports: u32,
    /// Import descriptors (module, field, kind).
    pub imports: Vec<Import>,
}

#[derive(Debug, Clone)]
pub struct Import {
    pub module: String,
    pub name: String,
    pub kind: ImportKind,
}

#[derive(Debug, Clone)]
pub enum ImportKind {
    Func(u32),       // type index
    Global { ty: ValType, mutable: bool },
    Memory(MemoryType),
    Table(TableDef),
}

#[derive(Debug)]
pub struct Func {
    pub type_idx: u32,
    pub locals: Vec<ValType>,
    pub body: Vec<Op>,
    /// Out-of-line BrTable data: (targets, default) indexed by Op.imm for OP_BR_TABLE.
    pub br_tables: Vec<(Vec<u32>, u32)>,
}

#[derive(Debug, Clone)]
pub struct MemoryType {
    pub min: u64,
    pub max: Option<u64>,
}

#[derive(Debug)]
pub struct GlobalDef {
    pub ty: ValType,
    pub mutable: bool,
    pub init: Vec<ConstOp>,
}

#[derive(Debug, Clone)]
pub struct Export {
    pub name: String,
    pub kind: ExportKind,
    pub index: u32,
}

#[derive(Debug, Clone)]
pub enum ExportKind {
    Func,
    Memory,
    Global,
    Table,
    Tag,
}

impl From<wasmparser::ExternalKind> for ExportKind {
    fn from(kind: wasmparser::ExternalKind) -> Self {
        match kind {
            wasmparser::ExternalKind::Func => Self::Func,
            wasmparser::ExternalKind::Memory => Self::Memory,
            wasmparser::ExternalKind::Global => Self::Global,
            wasmparser::ExternalKind::Table => Self::Table,
            wasmparser::ExternalKind::Tag => Self::Tag,
            _ => Self::Func, // unsupported kinds default to Func
        }
    }
}

#[derive(Debug)]
pub struct DataSegment {
    /// Offset expression for active segments; empty for passive segments.
    pub offset: Vec<ConstOp>,
    pub data: Vec<u8>,
    /// True for active segments that get applied to memory at instantiation.
    pub active: bool,
}

#[derive(Debug, Clone)]
pub struct TableDef {
    pub min: u64,
    pub max: Option<u64>,
    /// Init expression for each element (None = ref.null).
    pub init: Option<Vec<ConstOp>>,
    /// The element type of the table (funcref, externref, etc.).
    pub element_type: wasmparser::RefType,
}

#[derive(Debug)]
pub struct ElemSegment {
    pub table_idx: u32,
    pub offset: Vec<ConstOp>,
    /// Each item is either a direct func index or an expression needing evaluation.
    pub items: Vec<ElemItem>,
    /// True for active segments that get applied to a table at instantiation.
    pub active: bool,
}

#[derive(Debug, Clone)]
pub enum ElemItem {
    /// Direct function reference.
    Func(u32),
    /// Null reference.
    Null,
    /// Expression to evaluate at instantiation time (e.g. global.get for funcref).
    Expr(Vec<ConstOp>),
}

/// Accumulates parsed sections while walking through WASM payloads.
struct ModuleBuilder {
    types: Vec<FuncType>,
    memories: Vec<MemoryType>,
    globals: Vec<GlobalDef>,
    exports: Vec<Export>,
    data_segments: Vec<DataSegment>,
    func_types: Vec<u32>,
    tables: Vec<TableDef>,
    elements: Vec<ElemSegment>,
    start: Option<u32>,
    imports: Vec<Import>,
    num_func_imports: u32,
    num_global_imports: u32,
    num_memory_imports: u32,
    num_table_imports: u32,
    /// Pre-compiled function bodies: (locals, compiled ops, br_tables).
    func_bodies: Vec<(Vec<ValType>, Vec<Op>, Vec<(Vec<u32>, u32)>)>,
    code_idx: u32,
}

impl ModuleBuilder {
    fn new() -> Self {
        Self {
            types: Vec::new(),
            memories: Vec::new(),
            globals: Vec::new(),
            exports: Vec::new(),
            data_segments: Vec::new(),
            func_types: Vec::new(),
            tables: Vec::new(),
            elements: Vec::new(),
            start: None,
            imports: Vec::new(),
            num_func_imports: 0,
            num_global_imports: 0,
            num_memory_imports: 0,
            num_table_imports: 0,
            func_bodies: Vec::new(),
            code_idx: 0,
        }
    }

    /// Parse a single import entry and update the relevant index spaces.
    fn parse_single_import(&mut self, import: wasmparser::Import<'_>) -> Result<(), String> {
        let kind = match import.ty {
            wasmparser::TypeRef::Func(idx) => {
                self.func_types.push(idx);
                self.num_func_imports += 1;
                ImportKind::Func(idx)
            }
            wasmparser::TypeRef::Global(ty) => {
                self.num_global_imports += 1;
                ImportKind::Global { ty: ty.content_type, mutable: ty.mutable }
            }
            wasmparser::TypeRef::Memory(ty) => {
                self.memories.push(MemoryType { min: ty.initial, max: ty.maximum });
                self.num_memory_imports += 1;
                ImportKind::Memory(MemoryType { min: ty.initial, max: ty.maximum })
            }
            wasmparser::TypeRef::Table(ty) => {
                self.tables.push(TableDef { min: ty.initial, max: ty.maximum, init: None, element_type: ty.element_type });
                self.num_table_imports += 1;
                ImportKind::Table(TableDef { min: ty.initial, max: ty.maximum, init: None, element_type: ty.element_type })
            }
            _ => return Ok(()),
        };
        self.imports.push(Import {
            module: import.module.to_string(),
            name: import.name.to_string(),
            kind,
        });
        Ok(())
    }

    /// Parse a single element and push it onto `self.elements`.
    fn parse_element(&mut self, elem: wasmparser::Element<'_>) -> Result<(), String> {
        let items = parse_elem_items(&elem.items)?;
        match elem.kind {
            wasmparser::ElementKind::Active { table_index, offset_expr } => {
                let offset = decode_const_expr_multi(&offset_expr)?;
                self.elements.push(ElemSegment {
                    table_idx: table_index.unwrap_or(0),
                    offset,
                    items,
                    active: true,
                });
            }
            wasmparser::ElementKind::Passive => {
                self.elements.push(ElemSegment {
                    table_idx: 0,
                    offset: Vec::new(),
                    items,
                    active: false,
                });
            }
            wasmparser::ElementKind::Declared => {
                // Declared segments are dropped at instantiation
                // but still occupy an index in the element section.
                self.elements.push(ElemSegment {
                    table_idx: 0,
                    offset: Vec::new(),
                    items,
                    active: true, // treated as active so it gets dropped
                });
            }
        }
        Ok(())
    }

    /// Parse a single data segment entry.
    fn parse_data_segment(&mut self, data: wasmparser::Data<'_>) -> Result<(), String> {
        match data.kind {
            wasmparser::DataKind::Active { memory_index: 0, offset_expr } => {
                let offset = decode_const_expr_multi(&offset_expr)?;
                self.data_segments.push(DataSegment {
                    offset,
                    data: data.data.to_vec(),
                    active: true,
                });
            }
            wasmparser::DataKind::Passive => {
                self.data_segments.push(DataSegment {
                    offset: Vec::new(),
                    data: data.data.to_vec(),
                    active: false,
                });
            }
            _ => {
                // Active with memory_index != 0 — store but skip init
                self.data_segments.push(DataSegment {
                    offset: Vec::new(),
                    data: data.data.to_vec(),
                    active: false,
                });
            }
        }
        Ok(())
    }

    /// Decode a single code section entry, compiling directly to Op bytecode.
    fn parse_code_entry(&mut self, body: wasmparser::FunctionBody<'_>) -> Result<(), String> {
        let locals = self.collect_locals(&body)?;
        let ops_reader = body.get_operators_reader()
            .map_err(|e| format!("ops error: {e}"))?;
        let (compiled, br_tables) = compile_body(ops_reader, &self.types)?;
        self.func_bodies.push((locals, compiled, br_tables));
        self.code_idx += 1;
        Ok(())
    }

    /// Collect parameter types and declared locals for a function body.
    fn collect_locals(&self, body: &wasmparser::FunctionBody<'_>) -> Result<Vec<ValType>, String> {
        let type_idx = self.func_types[self.num_func_imports as usize + self.code_idx as usize];
        let func_type = &self.types[type_idx as usize];
        let mut locals: Vec<ValType> = func_type.params().to_vec();

        let local_reader = body.get_locals_reader()
            .map_err(|e| format!("locals error: {e}"))?;
        for local in local_reader {
            let (count, ty) = local.map_err(|e| format!("local error: {e}"))?;
            for _ in 0..count {
                locals.push(ty);
            }
        }
        Ok(locals)
    }

    /// Build Func entries from pre-compiled bodies.
    fn build_funcs(&self) -> Vec<Func> {
        self.func_bodies.iter().enumerate().map(|(i, (locals, compiled, br_tables))| {
            let type_idx = self.func_types[self.num_func_imports as usize + i];
            Func {
                type_idx,
                locals: locals.clone(),
                body: compiled.clone(),
                br_tables: br_tables.clone(),
            }
        }).collect()
    }

    /// Consume the builder and produce the final Module.
    fn build(self) -> Module {
        let funcs = self.build_funcs();
        Module {
            types: self.types,
            funcs,
            memories: self.memories,
            globals: self.globals,
            exports: self.exports,
            data_segments: self.data_segments,
            tables: self.tables,
            elements: self.elements,
            start: self.start,
            func_types: self.func_types,
            num_func_imports: self.num_func_imports,
            num_global_imports: self.num_global_imports,
            num_memory_imports: self.num_memory_imports,
            num_table_imports: self.num_table_imports,
            imports: self.imports,
        }
    }
}

impl Module {
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        let mut validator = wasmparser::Validator::new_with_features(
            wasmparser::WasmFeatures::default(),
        );
        let mut builder = ModuleBuilder::new();

        for payload in Parser::new(0).parse_all(bytes) {
            let payload = payload.map_err(|e| format!("parse error: {e}"))?;
            let valid = validator.payload(&payload)
                .map_err(|e| format!("validation error: {e}"))?;
            // For function bodies, the validator returns a FuncToValidate
            // that must be driven to completion to check the body's opcodes.
            if let wasmparser::ValidPayload::Func(func_validator, body) = valid {
                func_validator.into_validator(Default::default())
                    .validate(&body)
                    .map_err(|e| format!("validation error: {e}"))?;
            }
            dispatch_payload(&mut builder, payload)?;
        }

        Ok(builder.build())
    }

    /// Get a local function by global index (accounting for imports).
    pub fn get_func(&self, idx: u32) -> Option<&Func> {
        if idx < self.num_func_imports {
            None // imported function — not in self.funcs
        } else {
            self.funcs.get((idx - self.num_func_imports) as usize)
        }
    }

    /// Check if a function index refers to an import.
    pub fn is_import(&self, func_idx: u32) -> bool {
        func_idx < self.num_func_imports
    }

    pub fn export_func(&self, name: &str) -> Option<u32> {
        self.exports.iter().find_map(|e| {
            if e.name == name {
                if let ExportKind::Func = e.kind {
                    return Some(e.index);
                }
            }
            None
        })
    }
}

/// Route a single parsed payload to the appropriate builder method.
fn dispatch_payload(builder: &mut ModuleBuilder, payload: Payload<'_>) -> Result<(), String> {
    match payload {
        Payload::ImportSection(reader) => {
            for imports_group in reader {
                let imports_group = imports_group.map_err(|e| format!("import error: {e}"))?;
                for import in imports_group {
                    let (_offset, import) = import.map_err(|e| format!("import error: {e}"))?;
                    builder.parse_single_import(import)?;
                }
            }
        }
        Payload::TypeSection(reader) => {
            for ty in reader.into_iter_err_on_gc_types() {
                let ty = ty.map_err(|e| format!("type error: {e}"))?;
                builder.types.push(ty.clone());
            }
        }
        Payload::FunctionSection(reader) => {
            for type_idx in reader {
                let type_idx = type_idx.map_err(|e| format!("func error: {e}"))?;
                builder.func_types.push(type_idx);
            }
        }
        Payload::MemorySection(reader) => {
            for mem in reader {
                let mem = mem.map_err(|e| format!("memory error: {e}"))?;
                builder.memories.push(MemoryType { min: mem.initial, max: mem.maximum });
            }
        }
        Payload::GlobalSection(reader) => {
            for global in reader {
                let global = global.map_err(|e| format!("global error: {e}"))?;
                let init = decode_const_expr_multi(&global.init_expr)?;
                builder.globals.push(GlobalDef {
                    ty: global.ty.content_type,
                    mutable: global.ty.mutable,
                    init,
                });
            }
        }
        Payload::TableSection(reader) => {
            for table in reader {
                let table = table.map_err(|e| format!("table error: {e}"))?;
                let init = match table.init {
                    wasmparser::TableInit::RefNull => None,
                    wasmparser::TableInit::Expr(expr) => {
                        Some(decode_const_expr_multi(&expr)?)
                    }
                };
                builder.tables.push(TableDef {
                    min: table.ty.initial,
                    max: table.ty.maximum,
                    init,
                    element_type: table.ty.element_type,
                });
            }
        }
        Payload::ElementSection(reader) => {
            for elem in reader {
                let elem = elem.map_err(|e| format!("element error: {e}"))?;
                builder.parse_element(elem)?;
            }
        }
        Payload::StartSection { func, .. } => {
            builder.start = Some(func);
        }
        Payload::ExportSection(reader) => {
            for export in reader {
                let export = export.map_err(|e| format!("export error: {e}"))?;
                builder.exports.push(Export {
                    name: export.name.to_string(),
                    kind: ExportKind::from(export.kind),
                    index: export.index,
                });
            }
        }
        Payload::DataSection(reader) => {
            for data in reader {
                let data = data.map_err(|e| format!("data error: {e}"))?;
                builder.parse_data_segment(data)?;
            }
        }
        Payload::CodeSectionEntry(body) => {
            builder.parse_code_entry(body)?;
        }
        _ => {}
    }
    Ok(())
}

/// Parse element items from a wasmparser ElementItems into our ElemItem representation.
fn parse_elem_items(items: &wasmparser::ElementItems) -> Result<Vec<ElemItem>, String> {
    let mut result = Vec::new();
    match items {
        wasmparser::ElementItems::Functions(reader) => {
            for idx in reader.clone() {
                let idx = idx.map_err(|e| format!("elem func error: {e}"))?;
                result.push(ElemItem::Func(idx));
            }
        }
        wasmparser::ElementItems::Expressions(_, reader) => {
            for expr in reader.clone() {
                let expr = expr.map_err(|e| format!("elem expr error: {e}"))?;
                let const_ops = decode_const_expr_multi(&expr)?;
                if const_ops.len() == 1 {
                    match &const_ops[0] {
                        ConstOp::RefFunc(idx) => {
                            result.push(ElemItem::Func(*idx));
                            continue;
                        }
                        ConstOp::RefNull => {
                            result.push(ElemItem::Null);
                            continue;
                        }
                        _ => {}
                    }
                }
                if const_ops.is_empty() {
                    result.push(ElemItem::Null);
                } else {
                    result.push(ElemItem::Expr(const_ops));
                }
            }
        }
    }
    Ok(result)
}

/// Decode operators from a const expression into a list of ConstOps.
fn decode_const_expr_multi(expr: &wasmparser::ConstExpr) -> Result<Vec<ConstOp>, String> {
    let mut reader = expr.get_operators_reader();
    let mut ops = Vec::new();
    loop {
        let op = reader.read().map_err(|e| format!("const expr error: {e}"))?;
        match op {
            Operator::End => break,
            _ => {
                if let Some(const_op) = decode_const_op(&op) {
                    ops.push(const_op);
                } else {
                    return Err(format!("unsupported const expr op: {op:?}"));
                }
            }
        }
    }
    Ok(ops)
}
