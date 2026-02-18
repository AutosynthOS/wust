use wasmparser::{
    FuncType, Operator, Parser, Payload, ValType,
};

use crate::runtime::instruction::{
    BlockType, Instruction, Op, compile_body, resolve_block_targets,
};

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
    pub init: Vec<Instruction>,
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
}

#[derive(Debug)]
pub struct DataSegment {
    /// Offset expression for active segments; empty for passive segments.
    pub offset: Vec<Instruction>,
    pub data: Vec<u8>,
    /// True for active segments that get applied to memory at instantiation.
    pub active: bool,
}

#[derive(Debug, Clone)]
pub struct TableDef {
    pub min: u64,
    pub max: Option<u64>,
    /// Init expression for each element (None = ref.null).
    pub init: Option<Vec<Instruction>>,
}

#[derive(Debug)]
pub struct ElemSegment {
    pub table_idx: u32,
    pub offset: Vec<Instruction>,
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
    Expr(Vec<Instruction>),
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
    func_bodies: Vec<(Vec<ValType>, Vec<Instruction>)>,
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
                self.tables.push(TableDef { min: ty.initial, max: ty.maximum, init: None });
                self.num_table_imports += 1;
                ImportKind::Table(TableDef { min: ty.initial, max: ty.maximum, init: None })
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

    /// Decode a single code section entry into locals + instructions.
    fn parse_code_entry(&mut self, body: wasmparser::FunctionBody<'_>) -> Result<(), String> {
        let locals = self.collect_locals(&body)?;
        let instructions = decode_function_body(&body)?;
        self.func_bodies.push((locals, instructions));
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

    /// Compile function bodies into optimized Func entries.
    fn build_funcs(&self) -> Vec<Func> {
        self.func_bodies.iter().enumerate().map(|(i, (locals, instr_body))| {
            let type_idx = self.func_types[self.num_func_imports as usize + i];
            let mut body = instr_body.clone();
            peephole_optimize(&mut body);
            let (compiled, br_tables) = compile_body(&body, &self.types);
            Func { type_idx, locals: locals.clone(), body: compiled, br_tables }
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
        validate_module(bytes)?;
        let mut builder = ModuleBuilder::new();

        for payload in Parser::new(0).parse_all(bytes) {
            let payload = payload.map_err(|e| format!("parse error: {e}"))?;
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

/// Validate a WASM module's bytes before parsing.
fn validate_module(bytes: &[u8]) -> Result<(), String> {
    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::default())
        .validate_all(bytes)
        .map_err(|e| format!("validation error: {e}"))?;
    Ok(())
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
                let kind = match export.kind {
                    wasmparser::ExternalKind::Func => ExportKind::Func,
                    wasmparser::ExternalKind::Memory => ExportKind::Memory,
                    wasmparser::ExternalKind::Global => ExportKind::Global,
                    wasmparser::ExternalKind::Table => ExportKind::Table,
                    _ => continue,
                };
                builder.exports.push(Export {
                    name: export.name.to_string(),
                    kind,
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

/// Decode operators from a function body into a list of instructions.
fn decode_function_body(body: &wasmparser::FunctionBody<'_>) -> Result<Vec<Instruction>, String> {
    let ops_reader = body.get_operators_reader()
        .map_err(|e| format!("ops error: {e}"))?;
    let mut instructions = Vec::new();
    for op in ops_reader {
        let op = op.map_err(|e| format!("op error: {e}"))?;
        if let Some(instr) = decode_op(&op) {
            instructions.push(instr);
        }
    }
    resolve_block_targets(&mut instructions);
    Ok(instructions)
}

/// Peephole optimization pass: fuse common instruction sequences into superinstructions.
/// Replaces consumed instructions with Nop to preserve body length and all PC offsets.
fn peephole_optimize(body: &mut [Instruction]) {
    let len = body.len();
    let mut i = 0;
    while i + 1 < len {
        match (&body[i], &body[i + 1]) {
            // LocalGet + I32Const → LocalGetI32Const
            (Instruction::LocalGet(idx), Instruction::I32Const(val)) => {
                let idx = *idx;
                let val = *val;
                body[i] = Instruction::LocalGetI32Const(idx, val);
                body[i + 1] = Instruction::Nop;
                i += 2;
            }
            // LocalGet + LocalGet → LocalGetLocalGet
            (Instruction::LocalGet(a), Instruction::LocalGet(b)) => {
                let a = *a;
                let b = *b;
                body[i] = Instruction::LocalGetLocalGet(a, b);
                body[i + 1] = Instruction::Nop;
                i += 2;
            }
            _ => {
                i += 1;
            }
        }
    }
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
                let instrs = decode_const_expr_multi(&expr)?;
                if instrs.len() == 1 {
                    match &instrs[0] {
                        Instruction::RefFunc(idx) => {
                            result.push(ElemItem::Func(*idx));
                            continue;
                        }
                        Instruction::RefNull => {
                            result.push(ElemItem::Null);
                            continue;
                        }
                        _ => {}
                    }
                }
                if instrs.is_empty() {
                    result.push(ElemItem::Null);
                } else {
                    result.push(ElemItem::Expr(instrs));
                }
            }
        }
    }
    Ok(result)
}

fn decode_const_expr_multi(expr: &wasmparser::ConstExpr) -> Result<Vec<Instruction>, String> {
    let mut reader = expr.get_operators_reader();
    let mut instrs = Vec::new();
    loop {
        let op = reader.read().map_err(|e| format!("const expr error: {e}"))?;
        match op {
            Operator::End => break,
            _ => {
                if let Some(instr) = decode_op(&op) {
                    instrs.push(instr);
                } else {
                    return Err(format!("unsupported const expr op: {op:?}"));
                }
            }
        }
    }
    Ok(instrs)
}

fn decode_op(op: &Operator) -> Option<Instruction> {
    Some(match *op {
        Operator::Unreachable => Instruction::Unreachable,
        Operator::Nop => Instruction::Nop,
        Operator::Block { blockty } => Instruction::Block { ty: decode_block_type(blockty), end_pc: 0 },
        Operator::Loop { blockty } => Instruction::Loop { ty: decode_block_type(blockty) },
        Operator::If { blockty } => Instruction::If { ty: decode_block_type(blockty), end_pc: 0, else_pc: None },
        Operator::Else => Instruction::Else,
        Operator::End => Instruction::End,
        Operator::Br { relative_depth } => Instruction::Br(relative_depth),
        Operator::BrIf { relative_depth } => Instruction::BrIf(relative_depth),
        Operator::BrTable { ref targets } => Instruction::BrTable {
            targets: targets.targets().collect::<Result<Vec<_>, _>>().ok()?,
            default: targets.default(),
        },
        Operator::Return => Instruction::Return,
        Operator::Call { function_index } => Instruction::Call(function_index),
        Operator::CallIndirect { type_index, table_index } => Instruction::CallIndirect {
            type_idx: type_index,
            table_idx: table_index,
        },
        Operator::Drop => Instruction::Drop,
        Operator::Select => Instruction::Select,
        Operator::TypedSelect { .. } => Instruction::Select,

        Operator::LocalGet { local_index } => Instruction::LocalGet(local_index),
        Operator::LocalSet { local_index } => Instruction::LocalSet(local_index),
        Operator::LocalTee { local_index } => Instruction::LocalTee(local_index),
        Operator::GlobalGet { global_index } => Instruction::GlobalGet(global_index),
        Operator::GlobalSet { global_index } => Instruction::GlobalSet(global_index),

        Operator::I32Load { memarg } => Instruction::I32Load(memarg.offset),
        Operator::I64Load { memarg } => Instruction::I64Load(memarg.offset),
        Operator::F32Load { memarg } => Instruction::F32Load(memarg.offset),
        Operator::F64Load { memarg } => Instruction::F64Load(memarg.offset),
        Operator::I32Load8S { memarg } => Instruction::I32Load8S(memarg.offset),
        Operator::I32Load8U { memarg } => Instruction::I32Load8U(memarg.offset),
        Operator::I32Load16S { memarg } => Instruction::I32Load16S(memarg.offset),
        Operator::I32Load16U { memarg } => Instruction::I32Load16U(memarg.offset),
        Operator::I64Load8S { memarg } => Instruction::I64Load8S(memarg.offset),
        Operator::I64Load8U { memarg } => Instruction::I64Load8U(memarg.offset),
        Operator::I64Load16S { memarg } => Instruction::I64Load16S(memarg.offset),
        Operator::I64Load16U { memarg } => Instruction::I64Load16U(memarg.offset),
        Operator::I64Load32S { memarg } => Instruction::I64Load32S(memarg.offset),
        Operator::I64Load32U { memarg } => Instruction::I64Load32U(memarg.offset),
        Operator::I32Store { memarg } => Instruction::I32Store(memarg.offset),
        Operator::I64Store { memarg } => Instruction::I64Store(memarg.offset),
        Operator::F32Store { memarg } => Instruction::F32Store(memarg.offset),
        Operator::F64Store { memarg } => Instruction::F64Store(memarg.offset),
        Operator::I32Store8 { memarg } => Instruction::I32Store8(memarg.offset),
        Operator::I32Store16 { memarg } => Instruction::I32Store16(memarg.offset),
        Operator::I64Store8 { memarg } => Instruction::I64Store8(memarg.offset),
        Operator::I64Store16 { memarg } => Instruction::I64Store16(memarg.offset),
        Operator::I64Store32 { memarg } => Instruction::I64Store32(memarg.offset),
        Operator::MemorySize { .. } => Instruction::MemorySize,
        Operator::MemoryGrow { .. } => Instruction::MemoryGrow,

        Operator::I32Const { value } => Instruction::I32Const(value),
        Operator::I64Const { value } => Instruction::I64Const(value),
        Operator::F32Const { value } => Instruction::F32Const(f32::from_bits(value.bits())),
        Operator::F64Const { value } => Instruction::F64Const(f64::from_bits(value.bits())),

        Operator::I32Eqz => Instruction::I32Eqz,
        Operator::I32Eq => Instruction::I32Eq,
        Operator::I32Ne => Instruction::I32Ne,
        Operator::I32LtS => Instruction::I32LtS,
        Operator::I32LtU => Instruction::I32LtU,
        Operator::I32GtS => Instruction::I32GtS,
        Operator::I32GtU => Instruction::I32GtU,
        Operator::I32LeS => Instruction::I32LeS,
        Operator::I32LeU => Instruction::I32LeU,
        Operator::I32GeS => Instruction::I32GeS,
        Operator::I32GeU => Instruction::I32GeU,
        Operator::I32Clz => Instruction::I32Clz,
        Operator::I32Ctz => Instruction::I32Ctz,
        Operator::I32Popcnt => Instruction::I32Popcnt,
        Operator::I32Add => Instruction::I32Add,
        Operator::I32Sub => Instruction::I32Sub,
        Operator::I32Mul => Instruction::I32Mul,
        Operator::I32DivS => Instruction::I32DivS,
        Operator::I32DivU => Instruction::I32DivU,
        Operator::I32RemS => Instruction::I32RemS,
        Operator::I32RemU => Instruction::I32RemU,
        Operator::I32And => Instruction::I32And,
        Operator::I32Or => Instruction::I32Or,
        Operator::I32Xor => Instruction::I32Xor,
        Operator::I32Shl => Instruction::I32Shl,
        Operator::I32ShrS => Instruction::I32ShrS,
        Operator::I32ShrU => Instruction::I32ShrU,
        Operator::I32Rotl => Instruction::I32Rotl,
        Operator::I32Rotr => Instruction::I32Rotr,

        Operator::I64Eqz => Instruction::I64Eqz,
        Operator::I64Eq => Instruction::I64Eq,
        Operator::I64Ne => Instruction::I64Ne,
        Operator::I64LtS => Instruction::I64LtS,
        Operator::I64LtU => Instruction::I64LtU,
        Operator::I64GtS => Instruction::I64GtS,
        Operator::I64GtU => Instruction::I64GtU,
        Operator::I64LeS => Instruction::I64LeS,
        Operator::I64LeU => Instruction::I64LeU,
        Operator::I64GeS => Instruction::I64GeS,
        Operator::I64GeU => Instruction::I64GeU,
        Operator::I64Clz => Instruction::I64Clz,
        Operator::I64Ctz => Instruction::I64Ctz,
        Operator::I64Popcnt => Instruction::I64Popcnt,
        Operator::I64Add => Instruction::I64Add,
        Operator::I64Sub => Instruction::I64Sub,
        Operator::I64Mul => Instruction::I64Mul,
        Operator::I64DivS => Instruction::I64DivS,
        Operator::I64DivU => Instruction::I64DivU,
        Operator::I64RemS => Instruction::I64RemS,
        Operator::I64RemU => Instruction::I64RemU,
        Operator::I64And => Instruction::I64And,
        Operator::I64Or => Instruction::I64Or,
        Operator::I64Xor => Instruction::I64Xor,
        Operator::I64Shl => Instruction::I64Shl,
        Operator::I64ShrS => Instruction::I64ShrS,
        Operator::I64ShrU => Instruction::I64ShrU,
        Operator::I64Rotl => Instruction::I64Rotl,
        Operator::I64Rotr => Instruction::I64Rotr,

        Operator::I32WrapI64 => Instruction::I32WrapI64,
        Operator::I64ExtendI32S => Instruction::I64ExtendI32S,
        Operator::I64ExtendI32U => Instruction::I64ExtendI32U,

        Operator::F32Eq => Instruction::F32Eq,
        Operator::F32Ne => Instruction::F32Ne,
        Operator::F32Lt => Instruction::F32Lt,
        Operator::F32Gt => Instruction::F32Gt,
        Operator::F32Le => Instruction::F32Le,
        Operator::F32Ge => Instruction::F32Ge,
        Operator::F64Eq => Instruction::F64Eq,
        Operator::F64Ne => Instruction::F64Ne,
        Operator::F64Lt => Instruction::F64Lt,
        Operator::F64Gt => Instruction::F64Gt,
        Operator::F64Le => Instruction::F64Le,
        Operator::F64Ge => Instruction::F64Ge,
        Operator::F32Abs => Instruction::F32Abs,
        Operator::F32Neg => Instruction::F32Neg,
        Operator::F32Ceil => Instruction::F32Ceil,
        Operator::F32Floor => Instruction::F32Floor,
        Operator::F32Trunc => Instruction::F32Trunc,
        Operator::F32Nearest => Instruction::F32Nearest,
        Operator::F32Sqrt => Instruction::F32Sqrt,
        Operator::F32Add => Instruction::F32Add,
        Operator::F32Sub => Instruction::F32Sub,
        Operator::F32Mul => Instruction::F32Mul,
        Operator::F32Div => Instruction::F32Div,
        Operator::F32Min => Instruction::F32Min,
        Operator::F32Max => Instruction::F32Max,
        Operator::F32Copysign => Instruction::F32Copysign,
        Operator::F64Abs => Instruction::F64Abs,
        Operator::F64Neg => Instruction::F64Neg,
        Operator::F64Ceil => Instruction::F64Ceil,
        Operator::F64Floor => Instruction::F64Floor,
        Operator::F64Trunc => Instruction::F64Trunc,
        Operator::F64Nearest => Instruction::F64Nearest,
        Operator::F64Sqrt => Instruction::F64Sqrt,
        Operator::F64Add => Instruction::F64Add,
        Operator::F64Sub => Instruction::F64Sub,
        Operator::F64Mul => Instruction::F64Mul,
        Operator::F64Div => Instruction::F64Div,
        Operator::F64Min => Instruction::F64Min,
        Operator::F64Max => Instruction::F64Max,
        Operator::F64Copysign => Instruction::F64Copysign,

        Operator::I32TruncF32S => Instruction::I32TruncF32S,
        Operator::I32TruncF32U => Instruction::I32TruncF32U,
        Operator::I32TruncF64S => Instruction::I32TruncF64S,
        Operator::I32TruncF64U => Instruction::I32TruncF64U,
        Operator::I64TruncF32S => Instruction::I64TruncF32S,
        Operator::I64TruncF32U => Instruction::I64TruncF32U,
        Operator::I64TruncF64S => Instruction::I64TruncF64S,
        Operator::I64TruncF64U => Instruction::I64TruncF64U,
        Operator::F32ConvertI32S => Instruction::F32ConvertI32S,
        Operator::F32ConvertI32U => Instruction::F32ConvertI32U,
        Operator::F32ConvertI64S => Instruction::F32ConvertI64S,
        Operator::F32ConvertI64U => Instruction::F32ConvertI64U,
        Operator::F32DemoteF64 => Instruction::F32DemoteF64,
        Operator::F64ConvertI32S => Instruction::F64ConvertI32S,
        Operator::F64ConvertI32U => Instruction::F64ConvertI32U,
        Operator::F64ConvertI64S => Instruction::F64ConvertI64S,
        Operator::F64ConvertI64U => Instruction::F64ConvertI64U,
        Operator::F64PromoteF32 => Instruction::F64PromoteF32,
        Operator::I32ReinterpretF32 => Instruction::I32ReinterpretF32,
        Operator::I64ReinterpretF64 => Instruction::I64ReinterpretF64,
        Operator::F32ReinterpretI32 => Instruction::F32ReinterpretI32,
        Operator::F64ReinterpretI64 => Instruction::F64ReinterpretI64,

        Operator::I32Extend8S => Instruction::I32Extend8S,
        Operator::I32Extend16S => Instruction::I32Extend16S,
        Operator::I64Extend8S => Instruction::I64Extend8S,
        Operator::I64Extend16S => Instruction::I64Extend16S,
        Operator::I64Extend32S => Instruction::I64Extend32S,

        Operator::I32TruncSatF32S => Instruction::I32TruncSatF32S,
        Operator::I32TruncSatF32U => Instruction::I32TruncSatF32U,
        Operator::I32TruncSatF64S => Instruction::I32TruncSatF64S,
        Operator::I32TruncSatF64U => Instruction::I32TruncSatF64U,
        Operator::I64TruncSatF32S => Instruction::I64TruncSatF32S,
        Operator::I64TruncSatF32U => Instruction::I64TruncSatF32U,
        Operator::I64TruncSatF64S => Instruction::I64TruncSatF64S,
        Operator::I64TruncSatF64U => Instruction::I64TruncSatF64U,

        Operator::RefFunc { function_index } => Instruction::RefFunc(function_index),
        Operator::RefNull { .. } => Instruction::RefNull,

        Operator::RefIsNull => Instruction::RefIsNull,

        Operator::TableInit { elem_index, table } => Instruction::TableInit { elem_idx: elem_index, table_idx: table },
        Operator::ElemDrop { elem_index } => Instruction::ElemDrop(elem_index),
        Operator::MemoryInit { data_index, mem: 0 } => Instruction::MemoryInit(data_index),
        Operator::DataDrop { data_index } => Instruction::DataDrop(data_index),
        Operator::MemoryCopy { dst_mem: 0, src_mem: 0 } => Instruction::MemoryCopy,
        Operator::MemoryFill { mem: 0 } => Instruction::MemoryFill,

        Operator::TableGet { table } => Instruction::TableGet(table),
        Operator::TableSet { table } => Instruction::TableSet(table),
        Operator::TableGrow { table } => Instruction::TableGrow(table),
        Operator::TableSize { table } => Instruction::TableSize(table),
        Operator::TableCopy { dst_table, src_table } => Instruction::TableCopy { dst_table, src_table },
        Operator::TableFill { table } => Instruction::TableFill(table),

        _ => return None,
    })
}

fn decode_block_type(bt: wasmparser::BlockType) -> BlockType {
    match bt {
        wasmparser::BlockType::Empty => BlockType::Empty,
        wasmparser::BlockType::Type(ty) => BlockType::Val(ty),
        wasmparser::BlockType::FuncType(idx) => BlockType::FuncType(idx),
    }
}
