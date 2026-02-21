use std::cell::RefCell;
use std::rc::Rc;

use crate::runtime::code::module::{ConstOp, ElemItem, Module};
use crate::runtime::value::Value;

/// A shared, interior-mutable handle to a `Store`.
///
/// Allows multiple references to coexist (e.g. across core instances in
/// a component) while still permitting mutable access via `borrow_mut()`.
pub type SharedStore = Rc<RefCell<Store>>;

/// A shared table that can be imported across module instances.
///
/// When one module exports a table and another imports it, both instances
/// hold an `Rc` to the same underlying vector so mutations (e.g. element
/// segment initialization, `table.set`) are visible to both sides.
pub type SharedTable = Rc<RefCell<Vec<Option<u32>>>>;

const PAGE_SIZE: usize = 65536; // 64KB WASM pages

/// A host-provided function callable by imported WASM functions.
///
/// The second parameter is the module's linear memory (mutable), allowing
/// host functions to read data written by WASM code and write results
/// back (e.g. for fused adapter memory-based parameter passing).
pub type HostFunc = Box<dyn Fn(&[Value], &mut [u8]) -> Result<Vec<Value>, String>>;

/// Function indices >= this are external funcref callbacks stored in Store.extern_funcs.
pub const EXTERN_FUNC_BASE: u32 = 0x7FFF_0000;

/// Runtime instance state for an instantiated module.
pub struct Store {
    pub memory: Vec<u8>,
    /// Max memory size in pages (None = unlimited up to 4GB).
    pub memory_max: Option<u32>,
    pub globals: Vec<Value>,
    /// tables[i] = shared table; element j = function index (None = uninitialized).
    ///
    /// Tables are reference-counted so that imported tables share the same
    /// backing storage as the exporting instance.
    pub tables: Vec<SharedTable>,
    /// Host functions for imported function indices 0..num_func_imports.
    pub host_funcs: Vec<HostFunc>,
    /// Element segment data for table.init (None = dropped).
    pub elem_segments: Vec<Option<Vec<Option<u32>>>>,
    /// Data segment data for memory.init (None = dropped).
    pub data_segments: Vec<Option<Vec<u8>>>,
    /// External funcref callbacks (for cross-module function references).
    /// Indexed by (func_idx - EXTERN_FUNC_BASE).
    pub extern_funcs: Vec<HostFunc>,
    /// Table definitions (min/max sizes) for grow/size operations.
    pub table_defs: Vec<(u64, Option<u64>)>,
}

impl Store {
    /// Create a Store with no imports (for modules that don't import anything).
    pub fn new(module: &Module) -> Result<Self, String> {
        Self::new_with_imports(module, Vec::new(), Vec::new(), Vec::new())
    }

    /// Create a Store with imported globals, host functions, and shared tables.
    ///
    /// `imported_tables` contains one `SharedTable` for each table import the
    /// module declares (in declaration order). These are placed at the front
    /// of the tables vector, followed by any tables the module defines itself.
    pub fn new_with_imports(
        module: &Module,
        host_funcs: Vec<HostFunc>,
        imported_globals: Vec<Value>,
        imported_tables: Vec<SharedTable>,
    ) -> Result<Self, String> {
        // Init memory
        let mut memory = Vec::new();
        let mut memory_max = None;
        if let Some(mem) = module.memories.first() {
            memory.resize(mem.min as usize * PAGE_SIZE, 0);
            memory_max = mem.max.map(|m| m as u32);
        }

        // Init globals: imported globals first, then module-defined globals
        // (must be done before data segments since offsets may reference globals)
        let mut globals = imported_globals;
        for g in &module.globals {
            let val = eval_const_expr(&g.init, &globals).unwrap_or(Value::I32(0));
            globals.push(val);
        }

        // Init active data segments (copy data into memory)
        for seg in &module.data_segments {
            if seg.active {
                let offset = eval_const_expr(&seg.offset, &globals)
                    .and_then(|v| match v {
                        Value::I32(v) => Some(v as u32 as usize),
                        _ => None,
                    })
                    .ok_or("unsupported data segment offset expr")?;
                let end = offset
                    .checked_add(seg.data.len())
                    .ok_or("out of bounds memory access")?;
                if end > memory.len() {
                    return Err("out of bounds memory access".into());
                }
                memory[offset..end].copy_from_slice(&seg.data);
            }
        }

        // Init tables: imported tables first, then module-defined tables.
        // The module.tables vec includes entries for both imports and
        // definitions (imports come first, in declaration order).
        let num_table_imports = imported_tables.len();
        let mut tables: Vec<SharedTable> = imported_tables;
        for t in module.tables.iter().skip(num_table_imports) {
            let init_val = match &t.init {
                Some(instrs) => match eval_const_expr(instrs, &globals) {
                    Some(Value::FuncRef(func_ref)) => func_ref,
                    Some(Value::I32(v)) => Some(v as u32),
                    _ => None,
                },
                None => None,
            };
            tables.push(Rc::new(RefCell::new(vec![init_val; t.min as usize])));
        }

        // Apply active element segments to tables
        for elem in &module.elements {
            if elem.active {
                let offset = match eval_const_expr(&elem.offset, &globals) {
                    Some(Value::I32(v)) => v as u32 as usize,
                    _ => continue,
                };
                if let Some(shared_table) = tables.get(elem.table_idx as usize) {
                    let mut table = shared_table.borrow_mut();
                    let end = offset
                        .checked_add(elem.items.len())
                        .ok_or("out of bounds table access")?;
                    if end > table.len() {
                        return Err("out of bounds table access".into());
                    }
                    for (i, item) in elem.items.iter().enumerate() {
                        table[offset + i] = resolve_elem_item(item, &globals);
                    }
                }
            }
        }

        // Build elem_segments: active segments are implicitly dropped after init.
        let mut elem_segments: Vec<Option<Vec<Option<u32>>>> = Vec::new();
        for elem in &module.elements {
            let funcs: Vec<Option<u32>> = elem
                .items
                .iter()
                .map(|item| resolve_elem_item(item, &globals))
                .collect();
            if elem.active {
                elem_segments.push(None); // active segments are dropped after init
            } else {
                elem_segments.push(Some(funcs));
            }
        }

        // Build data_segments: active segments are dropped after init.
        let mut data_segments: Vec<Option<Vec<u8>>> = Vec::new();
        for seg in &module.data_segments {
            if seg.active {
                data_segments.push(None); // active segments are dropped after init
            } else {
                data_segments.push(Some(seg.data.clone()));
            }
        }

        // Store table definitions for grow/size
        let table_defs: Vec<(u64, Option<u64>)> =
            module.tables.iter().map(|t| (t.min, t.max)).collect();

        Ok(Store {
            memory,
            memory_max,
            globals,
            tables,
            host_funcs,
            elem_segments,
            data_segments,
            extern_funcs: Vec::new(),
            table_defs,
        })
    }

    pub fn memory_load<const N: usize>(&self, addr: u64) -> Result<[u8; N], &'static str> {
        let addr = addr as usize;
        if addr + N > self.memory.len() {
            return Err("out of bounds memory access");
        }
        let mut buf = [0u8; N];
        buf.copy_from_slice(&self.memory[addr..addr + N]);
        Ok(buf)
    }

    pub fn memory_store(&mut self, addr: u64, bytes: &[u8]) -> Result<(), &'static str> {
        let addr = addr as usize;
        if addr + bytes.len() > self.memory.len() {
            return Err("out of bounds memory access");
        }
        self.memory[addr..addr + bytes.len()].copy_from_slice(bytes);
        Ok(())
    }

    pub fn memory_grow(&mut self, pages: u32) -> i32 {
        let old_pages = (self.memory.len() / PAGE_SIZE) as u32;
        let new_pages = old_pages + pages;
        // Check max limit
        if let Some(max) = self.memory_max {
            if new_pages > max {
                return -1;
            }
        }
        let new_len = new_pages as usize * PAGE_SIZE;
        // Cap at 4GB
        if new_len > 4 * 1024 * 1024 * 1024 {
            return -1;
        }
        self.memory.resize(new_len, 0);
        old_pages as i32
    }

    pub fn memory_size(&self) -> i32 {
        (self.memory.len() / PAGE_SIZE) as i32
    }

    /// Register an external function callback and return its funcref index.
    pub fn add_extern_func(&mut self, func: HostFunc) -> u32 {
        let idx = EXTERN_FUNC_BASE + self.extern_funcs.len() as u32;
        self.extern_funcs.push(func);
        idx
    }
}

/// Pop two values of the same variant, apply a binary op, push the result.
macro_rules! const_binop {
    ($stack:expr, $variant:ident, $method:ident) => {{
        let Value::$variant(b) = $stack.pop()? else {
            return None;
        };
        let Value::$variant(a) = $stack.pop()? else {
            return None;
        };
        $stack.push(Value::$variant(a.$method(b)));
    }};
}

/// Evaluate a const expression to a Value, supporting all WASM types and extended const ops.
fn eval_const_expr(ops: &[ConstOp], globals: &[Value]) -> Option<Value> {
    let mut stack: Vec<Value> = Vec::new();
    for op in ops {
        match op {
            ConstOp::I32Const(v) => stack.push(Value::I32(*v)),
            ConstOp::I64Const(v) => stack.push(Value::I64(*v)),
            ConstOp::F32Const(v) => stack.push(Value::F32(*v)),
            ConstOp::F64Const(v) => stack.push(Value::F64(*v)),
            ConstOp::RefFunc(idx) => stack.push(Value::FuncRef(Some(*idx))),
            ConstOp::RefNull => stack.push(Value::FuncRef(None)),
            ConstOp::GlobalGet(idx) => {
                stack.push(*globals.get(*idx as usize)?);
            }
            ConstOp::I32Add => const_binop!(stack, I32, wrapping_add),
            ConstOp::I32Sub => const_binop!(stack, I32, wrapping_sub),
            ConstOp::I32Mul => const_binop!(stack, I32, wrapping_mul),
            ConstOp::I64Add => const_binop!(stack, I64, wrapping_add),
            ConstOp::I64Sub => const_binop!(stack, I64, wrapping_sub),
            ConstOp::I64Mul => const_binop!(stack, I64, wrapping_mul),
        }
    }
    stack.pop()
}

/// Resolve an element item to a function index, using globals for deferred expressions.
fn resolve_elem_item(item: &ElemItem, globals: &[Value]) -> Option<u32> {
    match item {
        ElemItem::Func(idx) => Some(*idx),
        ElemItem::Null => None,
        ElemItem::Expr(ops) => {
            // Evaluate expression — could be global.get for a funcref
            for op in ops {
                match op {
                    ConstOp::GlobalGet(idx) => match globals.get(*idx as usize) {
                        Some(&Value::FuncRef(func_ref)) => return func_ref,
                        Some(&Value::I32(v)) => return Some(v as u32),
                        _ => return None,
                    },
                    ConstOp::RefFunc(idx) => return Some(*idx),
                    ConstOp::RefNull => return None,
                    _ => {}
                }
            }
            None
        }
    }
}
