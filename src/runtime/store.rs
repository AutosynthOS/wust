use crate::runtime::module::{Instruction, Module};
use crate::runtime::value::Value;

const PAGE_SIZE: usize = 65536; // 64KB WASM pages

/// Evaluate a const expression (possibly multi-instruction) to an i32 offset.
fn eval_const_expr_i32(instrs: &[Instruction], globals: &[Value]) -> Option<i32> {
    let mut stack: Vec<i32> = Vec::new();
    for instr in instrs {
        match instr {
            Instruction::I32Const(v) => stack.push(*v),
            Instruction::GlobalGet(idx) => match globals.get(*idx as usize) {
                Some(&Value::I32(v)) => stack.push(v),
                _ => return None,
            },
            Instruction::I32Add => {
                let b = stack.pop()?;
                let a = stack.pop()?;
                stack.push(a.wrapping_add(b));
            }
            Instruction::I32Sub => {
                let b = stack.pop()?;
                let a = stack.pop()?;
                stack.push(a.wrapping_sub(b));
            }
            Instruction::I32Mul => {
                let b = stack.pop()?;
                let a = stack.pop()?;
                stack.push(a.wrapping_mul(b));
            }
            _ => return None,
        }
    }
    stack.pop()
}

/// A host-provided function callable by imported WASM functions.
pub type HostFunc = Box<dyn Fn(&[Value]) -> Vec<Value>>;

/// Runtime instance state for an instantiated module.
pub struct Store {
    pub memory: Vec<u8>,
    /// Max memory size in pages (None = unlimited up to 4GB).
    pub memory_max: Option<u32>,
    pub globals: Vec<Value>,
    /// tables[i][j] = function index at table i, element j (None = uninitialized)
    pub tables: Vec<Vec<Option<u32>>>,
    /// Host functions for imported function indices 0..num_func_imports.
    pub host_funcs: Vec<HostFunc>,
    /// Element segment data for table.init (None = dropped).
    pub elem_segments: Vec<Option<Vec<Option<u32>>>>,
}

impl Store {
    /// Create a Store with no imports (for modules that don't import anything).
    pub fn new(module: &Module) -> Result<Self, String> {
        Self::new_with_imports(module, Vec::new(), Vec::new())
    }

    /// Create a Store with imported globals and host functions.
    pub fn new_with_imports(
        module: &Module,
        host_funcs: Vec<HostFunc>,
        imported_globals: Vec<Value>,
    ) -> Result<Self, String> {
        // Init memory
        let mut memory = Vec::new();
        let mut memory_max = None;
        if let Some(mem) = module.memories.first() {
            memory.resize(mem.min as usize * PAGE_SIZE, 0);
            memory_max = mem.max.map(|m| m as u32);
        }

        // Init data segments
        for seg in &module.data_segments {
            let offset = match &seg.offset {
                Instruction::I32Const(v) => *v as usize,
                Instruction::GlobalGet(idx) => match imported_globals.get(*idx as usize) {
                    Some(&Value::I32(v)) => v as usize,
                    _ => return Err("unsupported data segment offset".into()),
                },
                _ => return Err("unsupported data segment offset expr".into()),
            };
            let end = offset + seg.data.len();
            if end > memory.len() {
                return Err("out of bounds memory access".into());
            }
            memory[offset..end].copy_from_slice(&seg.data);
        }

        // Init globals: imported globals first, then module-defined globals
        let mut globals = imported_globals;
        for g in &module.globals {
            let val = match &g.init {
                Instruction::I32Const(v) => Value::I32(*v),
                Instruction::I64Const(v) => Value::I64(*v),
                Instruction::F32Const(v) => Value::F32(*v),
                Instruction::F64Const(v) => Value::F64(*v),
                Instruction::GlobalGet(idx) => globals[*idx as usize],
                _ => Value::I32(0), // skip unsupported init exprs
            };
            globals.push(val);
        }

        // Init tables
        let mut tables: Vec<Vec<Option<u32>>> = module
            .tables
            .iter()
            .map(|t| vec![None; t.min as usize])
            .collect();

        // Apply element segments
        for elem in &module.elements {
            let offset = match eval_const_expr_i32(&elem.offset, &globals) {
                Some(v) => v as usize,
                None => continue,
            };
            if let Some(table) = tables.get_mut(elem.table_idx as usize) {
                if offset + elem.func_indices.len() > table.len() {
                    return Err("out of bounds table access".into());
                }
                for (i, &func_idx) in elem.func_indices.iter().enumerate() {
                    if func_idx == u32::MAX {
                        table[offset + i] = None; // ref.null
                    } else {
                        table[offset + i] = Some(func_idx);
                    }
                }
            }
        }

        // Build elem_segments: active segments are implicitly dropped after init.
        let mut elem_segments: Vec<Option<Vec<Option<u32>>>> = Vec::new();
        for (i, elem) in module.elements.iter().enumerate() {
            let funcs: Vec<Option<u32>> = elem.func_indices.iter().map(|&idx| {
                if idx == u32::MAX { None } else { Some(idx) }
            }).collect();
            // Active segments (those with an offset) are implicitly dropped
            let is_active = !elem.offset.is_empty();
            if is_active {
                elem_segments.push(None); // dropped
            } else {
                elem_segments.push(Some(funcs));
            }
            let _ = i; // suppress unused warning
        }

        Ok(Store { memory, memory_max, globals, tables, host_funcs, elem_segments })
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
}
