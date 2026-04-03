use std::cell::RefCell;
use std::collections::BTreeSet;
use std::rc::Rc;

use autosynth_graph::{AluOp, CmpOp, NodeRef, Op, Operand, Pool, SlotRef, VCode, VRegState};
use autosynth_isa::{PReg, Width};
use smallvec::smallvec;
use wust_core::{FRAME_HEADER_SIZE, FuncMeta, OpCode as WasmOp};

/// Shared pool reference — blocks and regions all create nodes in the same pool.
pub type SharedPool = Rc<RefCell<Pool>>;

/// ABI registers.
const G_LB: PReg = PReg(29); // locals base (frame pointer)
const G_SP: PReg = PReg(31); // fibre stack pointer
const G_LR: PReg = PReg(30); // link register

/// A contiguous region on the managed stack (locals, operands, fibre).
///
/// Tracks NodeRefs and their slot positions. Mirrors the real StackRegion
/// but creates nodes in a shared Pool.
#[derive(Clone)]
struct Region {
    base: PReg,
    base_offset: u16,
    cursor: u16,
    entries: Vec<NodeRef>,
    pool: SharedPool,
}

impl Region {
    fn new(base: PReg, base_offset: u16, pool: &SharedPool) -> Self {
        Self {
            base,
            base_offset,
            cursor: 0,
            entries: Vec::new(),
            pool: pool.clone(),
        }
    }

    /// Define a root value, then SetSlot it into this region.
    ///
    /// Returns the SetSlot NodeRef (what lives in the region).
    fn define(&mut self, state: VRegState) -> NodeRef {
        let width = state.width;
        // 1. Intern the root definition (no slot)
        let root = self.pool.borrow_mut().intern(state);
        // 2. SetSlot into this region position
        let slot = SlotRef {
            base: self.base,
            offset: (self.base_offset + self.cursor) as u32,
        };
        self.cursor += width.bytes() as u16;
        let with_slot = self.pool.borrow_mut().set_slot(root, slot);
        self.entries.push(with_slot.clone());
        with_slot
    }

    /// Push an existing NodeRef onto this region — emits a SetSlot node.
    fn push(&mut self, v: NodeRef) {
        let width = v.state().width;
        let slot = SlotRef {
            base: self.base,
            offset: (self.base_offset + self.cursor) as u32,
        };
        self.cursor += width.bytes() as u16;
        let with_slot = self.pool.borrow_mut().set_slot(v, slot);
        self.entries.push(with_slot);
    }

    /// Pop from this region — emits a ClearSlot node.
    fn pop(&mut self) -> Option<NodeRef> {
        let v = self.entries.pop()?;
        let width = v.state().width;
        self.cursor -= width.bytes() as u16;
        let cleared = self.pool.borrow_mut().clear_slot(v);
        Some(cleared)
    }

    fn get(&self, idx: usize) -> NodeRef {
        self.entries[idx].clone()
    }

    fn set(&mut self, idx: usize, v: NodeRef) {
        self.entries[idx] = v;
    }

    #[allow(dead_code)]
    fn len(&self) -> usize {
        self.entries.len()
    }
}

/// Per-block wasm state — regions tracking the managed stack layout.
///
/// ```text
/// g_lb + 0                        ← locals region start
///   [params][declared locals]
/// g_lb + locals_size              ← frame header
///   [FRAME HEADER (12 bytes)]
/// g_lb + locals_size + 12         ← operands region start
///   [operand stack ...]
///
/// g_sp + 0                        ← fibre region start
///   [link register][...]
/// ```
///
/// Cloning a WasmBlock snapshots the region state (for branch paths).
/// All clones share the same Pool — merging creates phi nodes in it.
#[derive(Clone)]
struct WasmBlock {
    locals: Region,
    operands: Region,
    fibre: Region,
    pool: SharedPool,
    /// Most recent side-effecting node in this block's effect chain.
    last_effect: Option<NodeRef>,
}

impl WasmBlock {
    fn new(locals_size: u16, pool: &SharedPool) -> Self {
        Self {
            locals: Region::new(G_LB, 0, pool),
            operands: Region::new(G_LB, locals_size + FRAME_HEADER_SIZE as u16, pool),
            fibre: Region::new(G_SP, 0, pool),
            pool: pool.clone(),
            last_effect: None,
        }
    }

    /// Merge another block's state into this one, creating phi nodes
    /// where values diverge.
    fn merge(&mut self, other: &WasmBlock, decision: NodeRef) {
        self.merge_entries(
            &mut self.locals.entries.clone(),
            &other.locals.entries,
            decision.clone(),
            true,
        );
        self.merge_entries(
            &mut self.operands.entries.clone(),
            &other.operands.entries,
            decision,
            false,
        );
    }

    fn merge_entries(
        &mut self,
        then_entries: &[NodeRef],
        else_entries: &[NodeRef],
        decision: NodeRef,
        is_locals: bool,
    ) {
        assert_eq!(then_entries.len(), else_entries.len());
        let target = if is_locals {
            &mut self.locals.entries
        } else {
            &mut self.operands.entries
        };
        for i in 0..then_entries.len() {
            if then_entries[i] != else_entries[i] {
                let width = then_entries[i].state().width;
                let phi = self.pool.borrow_mut().intern(VRegState {
                    op: Some(Op {
                        code: VCode::Phi,
                        uses: smallvec![
                            Operand::VReg(decision.clone()),
                            Operand::VReg(then_entries[i].clone()),
                            Operand::VReg(else_entries[i].clone()),
                        ],
                        effect: None,
                    }),
                    ..VRegState::new(width)
                });
                target[i] = phi;
            }
        }
    }
}

/// Minimal wasm graph builder — walks wasm bytecodes, outputs to a shared Pool.
///
/// Maintains wasm-level state via regions (locals, operands, fibre) that
/// mirror the managed stack ABI layout. No regalloc, no scheduling.
pub struct WasmGraphBuilder<'a> {
    pub pool: SharedPool,
    func: &'a FuncMeta,
    block: WasmBlock,
    /// Side-effect root nodes (returns, stores) — entry points for linearization.
    pub roots: Vec<NodeRef>,
}

impl<'a> WasmGraphBuilder<'a> {
    pub fn new(func: &'a FuncMeta) -> Self {
        let pool: SharedPool = Rc::new(RefCell::new(Pool::new()));
        let mut block = WasmBlock::new(func.locals_size, &pool);

        // Params — arrive in PRegs, dirty (register value newer than stack)
        for (i, _ty) in func.params.iter().enumerate() {
            let width = Width::W32; // TODO: derive from ValType
            block.locals.define(VRegState {
                preg: Some(PReg(i as u8)),
                dirty: true,
                ..VRegState::new(width)
            });
        }

        // Declared locals — const 0, dirty
        for _ty in func.locals.iter() {
            let width = Width::W32; // TODO: derive from ValType
            block.locals.define(VRegState {
                r#const: Some(0),
                dirty: true,
                ..VRegState::new(width)
            });
        }

        // Link register on fibre stack
        block.fibre.define(VRegState {
            preg: Some(G_LR),
            dirty: true,
            target: Some(G_LR),
            ..VRegState::new(Width::W64)
        });

        Self {
            pool,
            func,
            block,
            roots: Vec::new(),
        }
    }

    pub fn push(&mut self, v: NodeRef) {
        self.block.operands.push(v);
    }

    pub fn pop(&mut self) -> NodeRef {
        self.block.operands.pop().expect("operand stack underflow")
    }

    pub fn get_local(&self, index: usize) -> NodeRef {
        self.block.locals.get(index)
    }

    pub fn set_local(&mut self, index: usize, v: NodeRef) {
        self.block.locals.set(index, v);
    }

    /// The operand region entries (return values live here at function end).
    pub fn results(&self) -> Vec<NodeRef> {
        self.block.operands.entries.clone()
    }
}

/// Walk a function's bytecodes and build the graph.
///
/// `funcs` is needed to look up callee signatures for Call.
pub fn compile_to_graph<'a>(func: &'a FuncMeta, funcs: &[FuncMeta]) -> WasmGraphBuilder<'a> {
    let mut b = WasmGraphBuilder::new(func);

    // Block nesting: Vec of (decision, saved_block, has_else) triples.
    let mut nesting: Vec<(NodeRef, WasmBlock, bool)> = Vec::new();

    let mut pc = 0;
    loop {
        let inline_op = &func.body.ops[pc];
        let op = inline_op.opcode();

        match op {
            WasmOp::I32Const => {
                let val = inline_op.immediate_i32() as i64;
                let v = b.pool.borrow_mut().define_const(val, Width::W32);
                b.push(v);
            }
            WasmOp::LocalGetI32 => {
                let idx = inline_op.local_index() as usize;
                let v = b.get_local(idx);
                b.push(v);
            }
            WasmOp::LocalSetI32 => {
                let val = b.pop();
                let idx = inline_op.local_index() as usize;
                b.set_local(idx, val);
            }
            WasmOp::I32Add => {
                let rhs = b.pop();
                let lhs = b.pop();
                let v = b.pool.borrow_mut().binary(VCode::Alu(AluOp::Add), lhs, rhs);
                b.push(v);
            }
            WasmOp::I32Sub => {
                let rhs = b.pop();
                let lhs = b.pop();
                let v = b.pool.borrow_mut().binary(VCode::Alu(AluOp::Sub), lhs, rhs);
                b.push(v);
            }
            WasmOp::I32Mul => {
                let rhs = b.pop();
                let lhs = b.pop();
                let v = b.pool.borrow_mut().binary(VCode::Alu(AluOp::Mul), lhs, rhs);
                b.push(v);
            }
            WasmOp::I32Eqz => {
                let val = b.pop();
                let zero = b.pool.borrow_mut().define_const(0, Width::W32);
                let v = b
                    .pool
                    .borrow_mut()
                    .binary(VCode::Alu(AluOp::Cmp(CmpOp::Eq)), val, zero);
                b.push(v);
            }
            WasmOp::I32LeS => {
                let rhs = b.pop();
                let lhs = b.pop();
                let v = b
                    .pool
                    .borrow_mut()
                    .binary(VCode::Alu(AluOp::Cmp(CmpOp::LeS)), lhs, rhs);
                b.push(v);
            }
            WasmOp::Return => {
                // Wrap each return value in SetTarget (result N → wN)
                let mut uses = smallvec::SmallVec::<[Operand; 4]>::new();
                for i in 0..b.func.results.len() {
                    let val = b.pop();
                    let targeted = b.pool.borrow_mut().set_target(val, PReg(i as u8));
                    uses.push(Operand::VReg(targeted));
                }
                let ret = b.pool.borrow_mut().intern(VRegState {
                    op: Some(Op {
                        code: VCode::Return,
                        uses,
                        effect: b.block.last_effect.clone(),
                    }),
                    ..VRegState::new(Width::W32)
                });
                b.block.last_effect = Some(ret.clone());
                b.roots.push(ret);
            }
            WasmOp::Call => {
                let callee_idx = inline_op.immediate_u32();
                let callee = &funcs[callee_idx as usize];
                // Pop args, set target PReg on each (calling convention: arg N → wN)
                let mut raw_args: Vec<NodeRef> = Vec::new();
                for _ in 0..callee.params.len() {
                    raw_args.push(b.pop());
                }
                raw_args.reverse();
                let mut args = smallvec::SmallVec::<[Operand; 4]>::new();
                for (i, arg) in raw_args.into_iter().enumerate() {
                    let targeted = b.pool.borrow_mut().set_target(arg, PReg(i as u8));
                    args.push(Operand::VReg(targeted));
                }
                // Call is a side effect — no PReg, no value
                let call = b.pool.borrow_mut().intern(VRegState {
                    op: Some(Op {
                        code: VCode::Call(callee_idx),
                        uses: args,
                        effect: b.block.last_effect.clone(),
                    }),
                    ..VRegState::new(Width::W32)
                });
                b.block.last_effect = Some(call.clone());

                // Extract each result via UseCallResult — new root define
                for (i, _ty) in callee.results.iter().enumerate() {
                    let width = Width::W32; // TODO: derive from ValType
                    let result = b.pool.borrow_mut().intern(VRegState {
                        preg: Some(PReg(i as u8)),
                        dirty: true,
                        op: Some(Op {
                            code: VCode::UseCallResult,
                            uses: smallvec![Operand::VReg(call.clone())],
                            effect: None,
                        }),
                        ..VRegState::new(width)
                    });
                    b.push(result);
                }
            }
            WasmOp::If => {
                let cond = b.pop();
                let brif = b.pool.borrow_mut().intern(VRegState {
                    op: Some(Op {
                        code: VCode::BrIf,
                        uses: smallvec::smallvec![Operand::VReg(cond)],
                        effect: b.block.last_effect.clone(),
                    }),
                    ..VRegState::new(Width::W32)
                });
                b.block.last_effect = Some(brif.clone());
                let entry_block = b.block.clone();
                nesting.push((brif, entry_block, false));
            }
            WasmOp::Else => {
                let (_, entry_block, has_else) = nesting.last_mut().expect("no nesting");
                *has_else = true;
                let then_block = std::mem::replace(&mut b.block, entry_block.clone());
                *entry_block = then_block;
            }
            WasmOp::End => {
                let block_idx = inline_op.immediate_u32();
                if block_idx == 0 {
                    break;
                }

                let (decision, saved_block, has_else) = nesting.pop().expect("no nesting");

                if has_else {
                    // saved_block is the then-path (swapped at Else)
                    // b.block is the else-path
                    let else_block = b.block.clone();
                    b.block = saved_block;
                    b.block.merge(&else_block, decision);
                } else {
                    // No else — then-path may have terminated (return).
                    // Restore entry state for the continuation (false path).
                    // Track the decision — the continuation is guarded by it being false.
                    b.block = saved_block;
                }
            }
            _ => todo!("unhandled wasm opcode: {:?}", op),
        }

        pc += 1;
    }

    if !b.block.operands.entries.is_empty() {
        let mut uses = smallvec::SmallVec::<[Operand; 4]>::new();
        for (i, v) in b.block.operands.entries.iter().enumerate() {
            let targeted = b.pool.borrow_mut().set_target(v.clone(), PReg(i as u8));
            uses.push(Operand::VReg(targeted));
        }
        let ret = b.pool.borrow_mut().intern(VRegState {
            op: Some(Op {
                code: VCode::Return,
                uses,
                effect: b.block.last_effect.clone(),
            }),
            ..VRegState::new(Width::W32)
        });
        b.roots.push(ret);
    }

    b
}

// --- Block reconstruction from pool data only ---

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlockKind {
    Entry,
    /// Branch case — index corresponds to the phi use index (0 = then, 1 = else, ...).
    Case(u32),
    Merge,
}

pub struct Block {
    pub kind: BlockKind,
    pub ops: Vec<NodeRef>,
}

/// Reconstruct block structure from ONLY the pool and root nodes.
///
/// Splits on two kinds of divergence:
/// 1. Phi nodes — merge of then/else paths (if_result pattern)
/// 2. Multiple return roots — divergent exit paths (fib pattern)
///
/// Nodes are classified by reachability: exclusive to one path → that
/// path's block. Shared between paths → entry block.
pub fn reconstruct_blocks(_pool: &Pool, roots: &[NodeRef]) -> Vec<Block> {
    let mut all = BTreeSet::new();
    for root in roots {
        collect_reachable(root, &mut all);
    }

    // BrIf nodes and their dependencies are always Entry — they're
    // the control flow split points that ALL cases depend on.
    let mut entry_forced = BTreeSet::new();
    for v in &all {
        if let Some(op) = &v.state().op {
            if op.code == VCode::BrIf {
                collect_reachable(v, &mut entry_forced);
            }
        }
    }

    // Compute reachability from each root independently
    let root_reaches: Vec<BTreeSet<NodeRef>> = roots
        .iter()
        .map(|root| {
            let mut set = BTreeSet::new();
            collect_reachable(root, &mut set);
            set
        })
        .collect();

    // Classify each node
    let mut entry = BTreeSet::new();
    let mut case_blocks: Vec<BTreeSet<NodeRef>> = vec![BTreeSet::new(); roots.len()];

    for v in &all {
        // BrIf and its dependencies → always Entry
        if entry_forced.contains(v) {
            entry.insert(v.clone());
            continue;
        }

        let mut owning: Vec<usize> = Vec::new();
        for (i, reach) in root_reaches.iter().enumerate() {
            if reach.contains(v) {
                owning.push(i);
            }
        }

        match owning.len() {
            0 => {}
            1 => {
                case_blocks[owning[0]].insert(v.clone());
            }
            _ => {
                entry.insert(v.clone());
            }
        }
    }

    let mut blocks = vec![Block {
        kind: BlockKind::Entry,
        ops: topo_sort(&entry),
    }];

    for (i, case_set) in case_blocks.iter().enumerate() {
        if case_set.is_empty() {
            continue;
        }
        blocks.push(Block {
            kind: BlockKind::Case(i as u32),
            ops: topo_sort(case_set),
        });
    }

    blocks
}

/// Collect all nodes reachable by walking backwards from `root`.
/// Folded operands (UImm12 etc.) are not traversed — they have no NodeRef.
fn collect_reachable(root: &NodeRef, set: &mut BTreeSet<NodeRef>) {
    if !set.insert(root.clone()) {
        return;
    }
    if let Some(op) = &root.state().op {
        for u in &op.uses {
            if let Operand::VReg(r) = u {
                collect_reachable(r, set);
            }
        }
        // Follow effect chain
        if let Some(effect) = &op.effect {
            collect_reachable(effect, set);
        }
    }
}

/// Topological sort of a node set — post-order DFS respecting dependencies.
fn topo_sort(nodes: &BTreeSet<NodeRef>) -> Vec<NodeRef> {
    let mut visited = BTreeSet::new();
    let mut output = Vec::new();
    for node in nodes {
        topo_visit(node, nodes, &mut visited, &mut output);
    }
    output
}

fn topo_visit(
    v: &NodeRef,
    nodes: &BTreeSet<NodeRef>,
    visited: &mut BTreeSet<NodeRef>,
    output: &mut Vec<NodeRef>,
) {
    if !nodes.contains(v) || !visited.insert(v.clone()) {
        return;
    }
    if let Some(op) = &v.state().op {
        // Effect dependency first — ensures side-effect ordering
        if let Some(effect) = &op.effect {
            topo_visit(effect, nodes, visited, output);
        }
        for u in &op.uses {
            if let Operand::VReg(r) = u {
                topo_visit(r, nodes, visited, output);
            }
        }
    }
    output.push(v.clone());
}
