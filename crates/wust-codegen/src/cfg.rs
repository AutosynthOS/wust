/// Control-flow graph built from a flat IR instruction list.
///
/// The IR compiler emits a linear `Vec<IrInst>` with `DefLabel` markers
/// for branch targets. This module splits that list into basic blocks,
/// inserts explicit fallthrough branches where needed, and computes
/// predecessor/successor edges — producing the CFG structure that
/// regalloc2 requires.
use crate::ir::IrInst;

/// A basic block in the CFG.
#[derive(Debug)]
pub struct CfgBlock {
    /// First instruction index in `CfgInfo::insts` (inclusive).
    pub inst_start: u32,
    /// One past the last instruction index (exclusive).
    pub inst_end: u32,
    /// Successor block indices.
    pub succs: Vec<u32>,
    /// Predecessor block indices.
    pub preds: Vec<u32>,
}

/// Control-flow graph for an IR function.
///
/// Owns a (potentially modified) copy of the instruction list — the
/// original list may have had explicit `Br` instructions inserted at
/// fallthrough points so that every block ends with a terminator.
#[derive(Debug)]
pub struct CfgInfo {
    /// Instruction list (with fallthrough branches inserted).
    pub insts: Vec<IrInst>,
    /// Basic blocks, indexed by block ID.
    pub blocks: Vec<CfgBlock>,
}

/// Returns true if the instruction is a block terminator.
fn is_terminator(inst: &IrInst) -> bool {
    matches!(
        inst,
        IrInst::Br { .. }
            | IrInst::BrIfZero { .. }
            | IrInst::BrIfNonZero { .. }
            | IrInst::Return { .. }
            | IrInst::Trap
    )
}

/// Build a CFG from a flat IR instruction list.
///
/// Splits at `DefLabel` boundaries and after terminators, inserts
/// explicit `Br` for fallthrough edges, and computes pred/succ edges.
pub fn build_cfg(original_insts: &[IrInst]) -> CfgInfo {
    assert!(!original_insts.is_empty(), "empty IR instruction list");

    // Phase 1: find block split points (instruction indices where new
    // blocks start). A new block begins at index 0, at every DefLabel,
    // and at the instruction after every terminator.
    let mut split_set = Vec::new();
    let mut seen = vec![false; original_insts.len()];

    let mut mark = |idx: usize| {
        if !seen[idx] {
            seen[idx] = true;
            split_set.push(idx);
        }
    };

    mark(0);
    for (i, inst) in original_insts.iter().enumerate() {
        if matches!(inst, IrInst::DefLabel { .. }) {
            mark(i);
        }
        if is_terminator(inst) && i + 1 < original_insts.len() {
            mark(i + 1);
        }
    }

    split_set.sort_unstable();
    let splits = split_set;

    // Phase 2: copy instructions block-by-block, inserting Br at
    // fallthrough points so every block ends with a terminator.
    let mut new_insts: Vec<IrInst> = Vec::with_capacity(original_insts.len() + splits.len());
    let mut block_starts: Vec<usize> = Vec::with_capacity(splits.len());

    for (si, &start) in splits.iter().enumerate() {
        let end = if si + 1 < splits.len() {
            splits[si + 1]
        } else {
            original_insts.len()
        };

        block_starts.push(new_insts.len());
        new_insts.extend_from_slice(&original_insts[start..end]);

        let last = &original_insts[end - 1];
        if !is_terminator(last) {
            // Insert fallthrough branch. The next block must start
            // with a DefLabel so we know which label to target.
            assert!(
                si + 1 < splits.len(),
                "last block (starting at inst {start}) does not end with a terminator"
            );
            let next_start = splits[si + 1];
            match &original_insts[next_start] {
                IrInst::DefLabel { label } => {
                    new_insts.push(IrInst::Br { label: *label });
                }
                other => panic!(
                    "fallthrough to non-DefLabel instruction at index {next_start}: {other:?}"
                ),
            }
        }
    }

    // Phase 3: build CfgBlocks with instruction ranges and label map.
    let num_blocks = block_starts.len();
    let max_label = max_label_index(&new_insts);
    let mut label_to_block: Vec<Option<u32>> = vec![None; max_label + 1];
    let mut blocks: Vec<CfgBlock> = Vec::with_capacity(num_blocks);

    for (bi, &start) in block_starts.iter().enumerate() {
        let end = if bi + 1 < num_blocks {
            block_starts[bi + 1]
        } else {
            new_insts.len()
        };

        if let IrInst::DefLabel { label } = &new_insts[start] {
            label_to_block[label.0 as usize] = Some(bi as u32);
        }

        blocks.push(CfgBlock {
            inst_start: start as u32,
            inst_end: end as u32,
            succs: vec![],
            preds: vec![],
        });
    }

    // Phase 4: compute successors from each block's terminator.
    for bi in 0..num_blocks {
        let end = blocks[bi].inst_end as usize;
        let last = &new_insts[end - 1];

        let succs = match last {
            IrInst::Br { label } => {
                let target = label_to_block[label.0 as usize]
                    .unwrap_or_else(|| panic!("unresolved label L{}", label.0));
                vec![target]
            }
            IrInst::BrIfZero { label, .. } | IrInst::BrIfNonZero { label, .. } => {
                let target = label_to_block[label.0 as usize]
                    .unwrap_or_else(|| panic!("unresolved label L{}", label.0));
                let fallthrough = bi as u32 + 1;
                assert!(
                    (fallthrough as usize) < num_blocks,
                    "conditional branch at end of last block"
                );
                vec![fallthrough, target]
            }
            IrInst::Return { .. } | IrInst::Trap => vec![],
            other => panic!("block {bi} does not end with a terminator: {other:?}"),
        };

        blocks[bi].succs = succs;
    }

    // Phase 5: find reachable blocks via BFS from the entry block.
    // Dead code after Return/Trap can create blocks with no incoming
    // edges — these must be excluded so they don't add phantom
    // predecessors to real blocks (which would confuse regalloc2).
    let mut reachable = vec![false; num_blocks];
    let mut queue = std::collections::VecDeque::new();
    reachable[0] = true;
    queue.push_back(0usize);
    while let Some(bi) = queue.pop_front() {
        for &s in &blocks[bi].succs {
            let si = s as usize;
            if !reachable[si] {
                reachable[si] = true;
                queue.push_back(si);
            }
        }
    }

    // Clear successors on unreachable blocks so they don't pollute
    // predecessor lists.
    for bi in 0..num_blocks {
        if !reachable[bi] {
            blocks[bi].succs.clear();
        }
    }

    // Phase 6: compute predecessors by inverting successor edges.
    for bi in 0..num_blocks {
        let succs = blocks[bi].succs.clone();
        for s in succs {
            blocks[s as usize].preds.push(bi as u32);
        }
    }

    CfgInfo {
        insts: new_insts,
        blocks,
    }
}

/// Find the highest label index referenced in the instruction list.
pub(crate) fn max_label_index(insts: &[IrInst]) -> usize {
    let mut max = 0usize;
    for inst in insts {
        let l = match inst {
            IrInst::DefLabel { label }
            | IrInst::Br { label }
            | IrInst::BrIfZero { label, .. }
            | IrInst::BrIfNonZero { label, .. } => label.0 as usize,
            _ => continue,
        };
        if l > max {
            max = l;
        }
    }
    max
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Label, VReg};

    fn v(n: u32) -> VReg {
        VReg(n)
    }
    fn l(n: u32) -> Label {
        Label(n)
    }

    #[test]
    fn linear_function_produces_one_block() {
        let insts = vec![
            IrInst::IConst { dst: v(0), val: 42 },
            IrInst::Return {
                results: vec![v(0)],
            },
        ];

        let cfg = build_cfg(&insts);

        assert_eq!(cfg.blocks.len(), 1);
        assert_eq!(cfg.blocks[0].inst_start, 0);
        assert_eq!(cfg.blocks[0].inst_end, 2);
        assert!(cfg.blocks[0].succs.is_empty());
        assert!(cfg.blocks[0].preds.is_empty());
    }

    #[test]
    fn if_else_produces_four_blocks() {
        // Block 0: BrIfZero → L0 (else branch)
        // Block 1: then body, Br → L1 (end)
        // Block 2: DefLabel L0, else body, Br → L1 (end)
        // Block 3: DefLabel L1 (merge), Return
        let insts = vec![
            // Block 0
            IrInst::IConst { dst: v(0), val: 0 },
            IrInst::BrIfZero {
                cond: v(0),
                label: l(0),
            },
            // Block 1 (then)
            IrInst::IConst { dst: v(1), val: 1 },
            IrInst::FrameStore { slot: 0, src: v(1) },
            IrInst::Br { label: l(1) },
            // Block 2 (else)
            IrInst::DefLabel { label: l(0) },
            IrInst::IConst { dst: v(2), val: 2 },
            IrInst::FrameStore { slot: 0, src: v(2) },
            IrInst::Br { label: l(1) },
            // Block 3 (merge)
            IrInst::DefLabel { label: l(1) },
            IrInst::FrameLoad { dst: v(3), slot: 0 },
            IrInst::Return {
                results: vec![v(3)],
            },
        ];

        let cfg = build_cfg(&insts);

        assert_eq!(cfg.blocks.len(), 4);

        // Block 0: succs = [1 (fallthrough), 2 (else)]
        assert_eq!(cfg.blocks[0].succs, vec![1, 2]);
        assert!(cfg.blocks[0].preds.is_empty());

        // Block 1 (then): succs = [3 (end)], preds = [0]
        assert_eq!(cfg.blocks[1].succs, vec![3]);
        assert_eq!(cfg.blocks[1].preds, vec![0]);

        // Block 2 (else): succs = [3 (end)], preds = [0]
        assert_eq!(cfg.blocks[2].succs, vec![3]);
        assert_eq!(cfg.blocks[2].preds, vec![0]);

        // Block 3 (merge): succs = [], preds = [1, 2]
        assert!(cfg.blocks[3].succs.is_empty());
        assert_eq!(cfg.blocks[3].preds, vec![1, 2]);
    }

    #[test]
    fn fallthrough_inserts_br() {
        // A block that falls through to a DefLabel without an explicit Br.
        let insts = vec![
            IrInst::IConst { dst: v(0), val: 1 },
            IrInst::FrameStore { slot: 0, src: v(0) },
            // No Br here — fallthrough to L0
            IrInst::DefLabel { label: l(0) },
            IrInst::FrameLoad { dst: v(1), slot: 0 },
            IrInst::Return {
                results: vec![v(1)],
            },
        ];

        let cfg = build_cfg(&insts);

        assert_eq!(cfg.blocks.len(), 2);

        // Block 0 should have had a Br inserted, so it now has 3 instructions.
        assert_eq!(
            cfg.blocks[0].inst_end - cfg.blocks[0].inst_start,
            3,
            "expected fallthrough Br to be inserted"
        );
        // The inserted Br targets L0.
        let last_inst = &cfg.insts[cfg.blocks[0].inst_end as usize - 1];
        assert!(
            matches!(last_inst, IrInst::Br { label } if *label == l(0)),
            "expected Br to L0, got {last_inst:?}"
        );

        // Block 0 → Block 1
        assert_eq!(cfg.blocks[0].succs, vec![1]);
        assert_eq!(cfg.blocks[1].preds, vec![0]);
    }

    #[test]
    fn loop_produces_back_edge() {
        // Block 0: DefLabel L0 (loop header), body, BrIfNonZero → L0
        // Block 1: (fallthrough from BrIf), Return
        let insts = vec![
            IrInst::DefLabel { label: l(0) },
            IrInst::IConst { dst: v(0), val: 1 },
            IrInst::BrIfNonZero {
                cond: v(0),
                label: l(0),
            },
            // Block 1: exit
            IrInst::IConst { dst: v(1), val: 0 },
            IrInst::Return {
                results: vec![v(1)],
            },
        ];

        let cfg = build_cfg(&insts);

        assert_eq!(cfg.blocks.len(), 2);

        // Block 0: succs = [1 (fallthrough), 0 (back-edge)]
        assert_eq!(cfg.blocks[0].succs, vec![1, 0]);
        // Block 0 preds: [0] (self-loop)
        assert_eq!(cfg.blocks[0].preds, vec![0]);

        // Block 1: succs = [], preds = [0]
        assert!(cfg.blocks[1].succs.is_empty());
        assert_eq!(cfg.blocks[1].preds, vec![0]);
    }
}
