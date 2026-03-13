//! Debug trace collector for the codegen pipeline.
//!
//! The [`Debugger`] collects source-level annotations, IR instruction mappings,
//! and machine-level disassembly into a unified structure. All columns are
//! user-defined — the debugger has no hardcoded knowledge of "pc", "label",
//! "addr", or "asm". The caller configures columns via [`add_source_column`]
//! and [`add_machine_column`], then references them by name in all subsequent
//! calls.
//!
//! Source columns (e.g. pc, label, vstack snapshots) have one value per group.
//! Machine columns (e.g. addr, asm, operation) have one value per machine
//! instruction within a group.
//!
//! The final output is rendered via [`FunctionBox`](crate::disasm::boxes::FunctionBox)
//! and [`BlockBox`](crate::disasm::boxes::BlockBox) into a box-drawing visualization.

use std::collections::HashMap;

mod disasm;

use autosynth_ir::BlockId;
use disasm::boxes::{BlockBox, FunctionBox};
pub use disasm::table::{Align, Column, Row, Table};

/// Install a [`Debugger`] as the thread-local debug sink.
///
/// Any subsequent calls to [`autosynth_lower::dbg`] will forward to it.
pub fn install(debugger: Debugger) {
    autosynth_lower::install_dbg(Box::new(debugger));
}

/// Remove the thread-local debug sink and downcast it back to a [`Debugger`].
///
/// Returns `None` if no debugger was installed.
pub fn take() -> Option<Debugger> {
    let boxed = autosynth_lower::take_dbg()?;
    Some(
        *boxed
            .as_any()
            .downcast::<Debugger>()
            .expect("installed sink was not a Debugger"),
    )
}

/// Run a closure with the thread-local debugger, if one is installed.
///
/// This is a convenience wrapper that downcasts to [`Debugger`] for
/// source-level operations (add_source_column, set_pending, etc.).
/// For machine-level operations, use [`autosynth_lower::dbg`] directly.
pub fn dbg(f: impl FnOnce(&mut Debugger)) {
    autosynth_lower::dbg(|sink| {
        // SAFETY: if a Debugger was installed via install(), this downcast succeeds.
        let dbg = (sink as &mut dyn core::any::Any).downcast_mut::<Debugger>();
        if let Some(dbg) = dbg {
            f(dbg);
        }
    });
}

/// A single machine instruction within an [`OpGroup`].
struct MachineInst {
    /// Per-column values (one per machine column).
    values: Vec<Option<String>>,
}

/// A group of instructions corresponding to one IR emit.
struct OpGroup {
    /// Per-column source values (one per source column).
    source_values: Vec<Option<String>>,
    /// Machine instructions emitted for this group.
    machine_insts: Vec<MachineInst>,
}

/// Per-block debug metadata collected during compilation.
struct BlockDebugMeta {
    /// The block identifier.
    id: BlockId,
    /// Parameter descriptions (e.g. ["v4<i32>"]).
    params: Vec<String>,
    /// Result descriptions (e.g. ["v4<i32>", "v5<i32>"]).
    results: Vec<String>,
}

/// A debug trace collector for the codegen pipeline.
///
/// All columns are dynamic and referenced by name. Source columns are
/// registered via [`add_source_column`](Self::add_source_column) and machine
/// columns via [`add_machine_column`](Self::add_machine_column). Subsequent
/// calls use the column name (e.g. `"pc"`, `"asm"`) — no index newtypes.
///
/// # Phases
///
/// 1. **Setup**: Register source and machine columns by name.
/// 2. **Frontend**: [`set_pending`](Self::set_pending) annotates the next group,
///    [`record_ir_emit`](Self::record_ir_emit) creates groups.
/// 3. **Backend**: [`begin_ir_inst`](Self::begin_ir_inst) activates a group,
///    [`emit_machine_inst`](Self::emit_machine_inst) adds machine rows,
///    [`set_machine`](Self::set_machine) fills machine column values.
/// 4. **Render**: [`render`](Self::render) produces the visualization.
pub struct Debugger {
    /// Function signature for the header (e.g. "fib<0>(w9<i32>) -> w9<i32>").
    pub signature: String,
    /// Global register assignments (e.g. [("g.lb", "x29")]).
    pub globals: Vec<(String, String)>,
    /// Source column definitions (one value per group).
    source_columns: Vec<Column>,
    /// Source column name → index.
    source_index: HashMap<String, usize>,
    /// Machine column definitions (one value per machine instruction).
    machine_columns: Vec<Column>,
    /// Machine column name → index.
    machine_index: HashMap<String, usize>,
    /// All groups, in emission order.
    groups: Vec<OpGroup>,
    /// Maps IR instruction index to group index.
    ir_to_group: Vec<u32>,
    /// Currently open group index.
    current_group: Option<usize>,
    /// Pending source values for the next group.
    pending_source: Vec<Option<String>>,
    /// Block boundaries: (group_index, block_id).
    block_starts: Vec<(usize, BlockId)>,
    /// Per-block debug metadata.
    block_meta: Vec<BlockDebugMeta>,
}

impl Debugger {
    /// Create a new empty debugger with no columns.
    pub fn new() -> Self {
        Self {
            signature: String::new(),
            globals: Vec::new(),
            source_columns: Vec::new(),
            source_index: HashMap::new(),
            machine_columns: Vec::new(),
            machine_index: HashMap::new(),
            groups: Vec::new(),
            ir_to_group: Vec::new(),
            current_group: None,
            pending_source: Vec::new(),
            block_starts: Vec::new(),
            block_meta: Vec::new(),
        }
    }

    /// Register a source column (one value per group).
    ///
    /// The column is referenced by `name` in all subsequent calls.
    /// Registering the same name twice is a no-op.
    pub fn add_source_column(&mut self, name: &str, align: Align) {
        if self.source_index.contains_key(name) {
            return;
        }
        let idx = self.source_columns.len();
        self.source_columns.push(Column {
            header: name.to_string(),
            align,
        });
        self.source_index.insert(name.to_string(), idx);
        self.pending_source.push(None);
    }

    /// Register a machine column (one value per machine instruction).
    ///
    /// The column is referenced by `name` in all subsequent calls.
    /// Registering the same name twice is a no-op.
    pub fn add_machine_column(&mut self, name: &str, align: Align) {
        if self.machine_index.contains_key(name) {
            return;
        }
        let idx = self.machine_columns.len();
        self.machine_columns.push(Column {
            header: name.to_string(),
            align,
        });
        self.machine_index.insert(name.to_string(), idx);
    }

    /// Set a pending source column value for the next group.
    ///
    /// Consumed by the next [`record_ir_emit`](Self::record_ir_emit) call.
    /// Silently ignored if the column name was never registered.
    pub fn set_pending(&mut self, col: &str, value: &str) {
        if let Some(&idx) = self.source_index.get(col) {
            self.pending_source[idx] = Some(value.to_string());
        }
    }

    /// Set a source column value on the current group (after emit).
    ///
    /// Use this for values that are only known after the IR instruction
    /// is emitted, such as operation notes.
    pub fn set_source(&mut self, col: &str, value: &str) {
        if let (Some(&idx), Some(group_idx)) = (self.source_index.get(col), self.current_group) {
            let group = &mut self.groups[group_idx];
            while group.source_values.len() <= idx {
                group.source_values.push(None);
            }
            group.source_values[idx] = Some(value.to_string());
        }
    }

    /// Record a block boundary at the current group index.
    pub fn mark_block_start(&mut self, id: BlockId) {
        let group_idx = self.groups.len();
        self.block_starts.push((group_idx, id));
    }

    /// Store per-block metadata (params and results) for rendering.
    pub fn set_block_meta(&mut self, id: BlockId, params: Vec<String>, results: Vec<String>) {
        self.block_meta.push(BlockDebugMeta {
            id,
            params,
            results,
        });
    }

    /// Create a standalone annotation group with just an operation label.
    ///
    /// Unlike [`record_ir_emit`](Self::record_ir_emit), this does NOT
    /// map to an IR index. Consumes pending source values so pc/label
    /// appear once. Use for bookkeeping annotations (push, pop, field
    /// access) that should appear as their own rows.
    pub fn note(&mut self, text: &str) {
        let mut source_values = std::mem::replace(
            &mut self.pending_source,
            vec![None; self.source_columns.len()],
        );
        if let Some(&idx) = self.source_index.get("operation") {
            source_values[idx] = Some(text.to_string());
        }
        let group_idx = self.groups.len();
        self.groups.push(OpGroup {
            source_values,
            machine_insts: Vec::new(),
        });
        self.current_group = Some(group_idx);
    }

    /// Map the next IR instruction index to a new group.
    ///
    /// Always creates a new group, consuming any pending source values.
    pub fn record_ir_emit(&mut self) {
        let source_values = std::mem::replace(
            &mut self.pending_source,
            vec![None; self.source_columns.len()],
        );

        let idx = self.groups.len();

        self.groups.push(OpGroup {
            source_values,
            machine_insts: Vec::new(),
        });
        self.current_group = Some(idx);
        self.ir_to_group.push(idx as u32);
    }

    /// Activate the group corresponding to an IR instruction index.
    ///
    /// Called by the backend before emitting machine instructions for a
    /// given IR instruction.
    pub fn begin_ir_inst(&mut self, ir_index: usize) {
        if let Some(&group_idx) = self.ir_to_group.get(ir_index) {
            self.current_group = Some(group_idx as usize);
        }
    }

    /// Append a machine instruction row to the current group.
    ///
    /// Creates an empty row — use [`set_machine`](Self::set_machine)
    /// to fill in column values.
    pub fn emit_machine_inst(&mut self) {
        if let Some(idx) = self.current_group {
            self.groups[idx].machine_insts.push(MachineInst {
                values: vec![None; self.machine_columns.len()],
            });
        }
    }

    /// Set a machine column value on the last machine instruction.
    ///
    /// Silently ignored if the column name was never registered.
    pub fn set_machine(&mut self, col: &str, value: &str) {
        if let Some(&col_idx) = self.machine_index.get(col) {
            if let Some(group_idx) = self.current_group {
                if let Some(inst) = self.groups[group_idx].machine_insts.last_mut() {
                    while inst.values.len() <= col_idx {
                        inst.values.push(None);
                    }
                    inst.values[col_idx] = Some(value.to_string());
                }
            }
        }
    }

    /// Render the collected debug trace as a box-drawing visualization.
    pub fn render(&self) -> String {
        let columns = self.build_columns();
        let num_source = self.source_columns.len();
        let num_machine = self.machine_columns.len();

        let total_groups = self.groups.len();
        let mut blocks = Vec::new();

        for (block_idx, &(group_start, block_id)) in self.block_starts.iter().enumerate() {
            let group_end = self
                .block_starts
                .get(block_idx + 1)
                .map(|&(gs, _)| gs)
                .unwrap_or(total_groups);

            let mut rows = Vec::new();
            for group in &self.groups[group_start..group_end] {
                rows.extend(render_group_rows(group, num_source, num_machine));
            }

            let meta = self.block_meta.iter().find(|m| m.id == block_id);
            let (params, results) = match meta {
                Some(m) => (m.params.clone(), m.results.clone()),
                None => (Vec::new(), Vec::new()),
            };

            blocks.push(BlockBox {
                id: block_id,
                params,
                results,
                table: Table {
                    columns: columns.clone(),
                    rows,
                },
            });
        }

        // Handle orphan groups before any block_start.
        let first_block_start = self.block_starts.first().map(|&(gs, _)| gs).unwrap_or(0);
        if first_block_start > 0 && !self.groups[..first_block_start].is_empty() {
            let mut rows = Vec::new();
            for group in &self.groups[..first_block_start] {
                rows.extend(render_group_rows(group, num_source, num_machine));
            }
            let orphan = BlockBox {
                id: BlockId::Gen(9999),
                params: Vec::new(),
                results: Vec::new(),
                table: Table {
                    columns: columns.clone(),
                    rows,
                },
            };
            blocks.insert(0, orphan);
        }

        let func_box = FunctionBox {
            signature: self.signature.clone(),
            globals: self.globals.clone(),
            blocks,
        };

        func_box.render()
    }

    /// Build the combined column definitions: [source_columns..., machine_columns...].
    fn build_columns(&self) -> Vec<Column> {
        let mut cols = self.source_columns.clone();
        cols.extend(self.machine_columns.iter().cloned());
        cols
    }
}

impl autosynth_lower::DbgSink for Debugger {
    fn begin_ir_inst(&mut self, ir_index: usize) {
        self.begin_ir_inst(ir_index);
    }

    fn emit_machine_inst(&mut self) {
        self.emit_machine_inst();
    }

    fn set_machine(&mut self, col: &str, value: &str) {
        self.set_machine(col, value);
    }

    fn current_group(&self) -> usize {
        self.current_group.unwrap_or(0)
    }

    fn set_current_group(&mut self, group: usize) {
        self.current_group = Some(group);
    }

    fn as_any(self: Box<Self>) -> Box<dyn std::any::Any> {
        self
    }
}

/// Convert an [`OpGroup`] into one or more [`Row`]s for the debug table.
fn render_group_rows(group: &OpGroup, num_source: usize, num_machine: usize) -> Vec<Row> {
    let mut rows = Vec::new();

    let source_cells: Vec<Option<String>> = (0..num_source)
        .map(|i| group.source_values.get(i).cloned().flatten())
        .collect();

    let empty_source: Vec<Option<String>> = vec![None; num_source];

    if group.machine_insts.is_empty() {
        let mut cells = source_cells;
        cells.extend(vec![None; num_machine]);
        rows.push(Row { cells });
    } else {
        let first = &group.machine_insts[0];
        let mut cells = source_cells;
        for i in 0..num_machine {
            cells.push(first.values.get(i).cloned().flatten());
        }
        rows.push(Row { cells });

        for inst in &group.machine_insts[1..] {
            let mut cells = empty_source.clone();
            for i in 0..num_machine {
                cells.push(inst.values.get(i).cloned().flatten());
            }
            rows.push(Row { cells });
        }
    }

    rows
}
