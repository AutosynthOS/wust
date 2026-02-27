/// Adapter that implements `regalloc2::Function` for our IR + CFG.
///
/// Pre-computes per-instruction operands, per-block ranges, and
/// successor/predecessor lists from a `CfgInfo`. This is the bridge
/// between our IR representation and regalloc2's allocation engine.
use regalloc2::{
    self, Block, Inst, InstRange, MachineEnv, Operand, PReg, PRegSet, RegClass, VReg,
};

use crate::cfg::CfgInfo;
use crate::ir::IrInst;

/// Wraps a `CfgInfo` for regalloc2.
pub struct RegAllocAdapter {
    num_insts: usize,
    num_vregs: usize,

    /// Per-block instruction ranges.
    block_ranges: Vec<InstRange>,
    /// Per-block successors (as regalloc2 Block indices).
    block_succs: Vec<Vec<Block>>,
    /// Per-block predecessors (as regalloc2 Block indices).
    block_preds: Vec<Vec<Block>>,

    /// Per-instruction operands (uses and defs).
    operands: Vec<Vec<Operand>>,
    /// Per-instruction clobber sets.
    clobbers: Vec<PRegSet>,
    /// Which instructions are branches.
    is_branch_flags: Vec<bool>,
    /// Which instructions are returns.
    is_ret_flags: Vec<bool>,
}

/// Convert our IR VReg to a regalloc2 VReg (all integer class).
fn to_ra2_vreg(v: crate::ir::VReg) -> VReg {
    VReg::new(v.0 as usize, RegClass::Int)
}

/// Physical registers for wasm call arguments: x9, x10, x11, ...
fn arg_preg(i: usize) -> PReg {
    PReg::new(9 + i, RegClass::Int)
}

/// Build the set of all allocatable physical registers (for clobber sets).
fn allocatable_set() -> PRegSet {
    let mut set = PRegSet::empty();
    // x0–x14 are allocatable (x15 is scratch for move resolution).
    for i in 0..15 {
        set.add(PReg::new(i, RegClass::Int));
    }
    set
}

impl RegAllocAdapter {
    /// Build the adapter from a CFG and IR function metadata.
    pub fn new(cfg: &CfgInfo) -> Self {
        let num_insts = cfg.insts.len();
        let num_blocks = cfg.blocks.len();

        // Count VRegs.
        let num_vregs = count_vregs(&cfg.insts);

        // Pre-compute per-block data.
        let mut block_ranges = Vec::with_capacity(num_blocks);
        let mut block_succs = Vec::with_capacity(num_blocks);
        let mut block_preds = Vec::with_capacity(num_blocks);

        for block in &cfg.blocks {
            block_ranges.push(InstRange::new(
                Inst::new(block.inst_start as usize),
                Inst::new(block.inst_end as usize),
            ));
            block_succs.push(block.succs.iter().map(|&s| Block::new(s as usize)).collect());
            block_preds.push(block.preds.iter().map(|&p| Block::new(p as usize)).collect());
        }

        // Pre-compute per-instruction operands, clobbers, and flags.
        let clobber_set = allocatable_set();
        let mut operands = Vec::with_capacity(num_insts);
        let mut clobbers = Vec::with_capacity(num_insts);
        let mut is_branch_flags = Vec::with_capacity(num_insts);
        let mut is_ret_flags = Vec::with_capacity(num_insts);

        for inst in &cfg.insts {
            let (ops, clob, is_br, is_rt) = classify_inst(inst, &clobber_set);
            operands.push(ops);
            clobbers.push(clob);
            is_branch_flags.push(is_br);
            is_ret_flags.push(is_rt);
        }

        RegAllocAdapter {
            num_insts,
            num_vregs,
            block_ranges,
            block_succs,
            block_preds,
            operands,
            clobbers,
            is_branch_flags,
            is_ret_flags,
        }
    }
}

/// Classify a single IR instruction into regalloc2 metadata.
///
/// Returns (operands, clobbers, is_branch, is_return).
fn classify_inst(
    inst: &IrInst,
    clobber_set: &PRegSet,
) -> (Vec<Operand>, PRegSet, bool, bool) {
    let empty_clob = PRegSet::empty();

    match inst {
        IrInst::IConst { dst, .. } => (vec![Operand::reg_def(to_ra2_vreg(*dst))], empty_clob, false, false),

        IrInst::ParamDef { dst, idx } => (
            vec![Operand::reg_fixed_def(to_ra2_vreg(*dst), arg_preg(*idx as usize))],
            empty_clob,
            false,
            false,
        ),

        IrInst::LocalGet { dst, .. } => (vec![Operand::reg_def(to_ra2_vreg(*dst))], empty_clob, false, false),

        IrInst::LocalSet { src, .. } => (vec![Operand::reg_use(to_ra2_vreg(*src))], empty_clob, false, false),

        IrInst::Add { dst, lhs, rhs } | IrInst::Sub { dst, lhs, rhs } => (
            vec![
                Operand::reg_def(to_ra2_vreg(*dst)),
                Operand::reg_use(to_ra2_vreg(*lhs)),
                Operand::reg_use(to_ra2_vreg(*rhs)),
            ],
            empty_clob,
            false,
            false,
        ),

        IrInst::AddImm { dst, lhs, .. } | IrInst::SubImm { dst, lhs, .. } => (
            vec![
                Operand::reg_def(to_ra2_vreg(*dst)),
                Operand::reg_use(to_ra2_vreg(*lhs)),
            ],
            empty_clob,
            false,
            false,
        ),

        IrInst::Cmp { dst, lhs, rhs, .. } => (
            vec![
                Operand::reg_def(to_ra2_vreg(*dst)),
                Operand::reg_use(to_ra2_vreg(*lhs)),
                Operand::reg_use(to_ra2_vreg(*rhs)),
            ],
            empty_clob,
            false,
            false,
        ),

        IrInst::CmpImm { dst, lhs, .. } => (
            vec![
                Operand::reg_def(to_ra2_vreg(*dst)),
                Operand::reg_use(to_ra2_vreg(*lhs)),
            ],
            empty_clob,
            false,
            false,
        ),

        IrInst::DefLabel { .. } => (vec![], empty_clob, false, false),

        IrInst::Br { .. } => (vec![], empty_clob, true, false),

        IrInst::BrIfZero { cond, .. } | IrInst::BrIfNonZero { cond, .. } => (
            vec![Operand::reg_use(to_ra2_vreg(*cond))],
            empty_clob,
            true,
            false,
        ),

        IrInst::FrameStore { src, .. } => (vec![Operand::reg_use(to_ra2_vreg(*src))], empty_clob, false, false),

        IrInst::FrameLoad { dst, .. } => (vec![Operand::reg_def(to_ra2_vreg(*dst))], empty_clob, false, false),

        IrInst::Call { args, result, .. } => {
            let mut ops = Vec::with_capacity(args.len() + 1);
            for (i, arg) in args.iter().enumerate() {
                ops.push(Operand::reg_fixed_use(to_ra2_vreg(*arg), arg_preg(i)));
            }
            if let Some(r) = result {
                // Result is defined in x9 (arg_preg(0)).
                ops.push(Operand::reg_fixed_def(to_ra2_vreg(*r), arg_preg(0)));
            }
            // Call clobbers all allocatable registers EXCEPT those that
            // appear as explicit operands. Clobbers tell regalloc2 that
            // these registers are trashed; operand registers are already
            // tracked via their use/def constraints.
            let mut clob = *clobber_set;
            for (i, _) in args.iter().enumerate() {
                clob.remove(arg_preg(i));
            }
            if result.is_some() {
                clob.remove(arg_preg(0));
            }
            (ops, clob, false, false)
        }

        IrInst::Return { results } => {
            let ops: Vec<Operand> = results
                .iter()
                .enumerate()
                .map(|(i, r)| Operand::reg_fixed_use(to_ra2_vreg(*r), arg_preg(i)))
                .collect();
            (ops, empty_clob, true, true)
        }

        IrInst::FuelConsume { .. } | IrInst::FuelCheck => (vec![], empty_clob, false, false),

        IrInst::Trap => (vec![], empty_clob, false, true),
    }
}

/// Count VRegs referenced in the instruction list (max index + 1).
fn count_vregs(insts: &[IrInst]) -> usize {
    let mut max = 0u32;
    for inst in insts {
        inst.for_each_def(|v| max = max.max(v.0 + 1));
        inst.for_each_use(|v| max = max.max(v.0 + 1));
    }
    max as usize
}

impl regalloc2::Function for RegAllocAdapter {
    fn num_insts(&self) -> usize {
        self.num_insts
    }

    fn num_blocks(&self) -> usize {
        self.block_ranges.len()
    }

    fn entry_block(&self) -> Block {
        Block::new(0)
    }

    fn block_insns(&self, block: Block) -> InstRange {
        self.block_ranges[block.index()]
    }

    fn block_succs(&self, block: Block) -> &[Block] {
        &self.block_succs[block.index()]
    }

    fn block_preds(&self, block: Block) -> &[Block] {
        &self.block_preds[block.index()]
    }

    fn block_params(&self, _block: Block) -> &[VReg] {
        // No block parameters yet — merge values go through
        // FrameStore/FrameLoad in memory.
        &[]
    }

    fn is_ret(&self, insn: Inst) -> bool {
        self.is_ret_flags[insn.index()]
    }

    fn is_branch(&self, insn: Inst) -> bool {
        self.is_branch_flags[insn.index()]
    }

    fn branch_blockparams(&self, _block: Block, _insn: Inst, _succ_idx: usize) -> &[VReg] {
        // No block parameters yet.
        &[]
    }

    fn inst_operands(&self, insn: Inst) -> &[Operand] {
        &self.operands[insn.index()]
    }

    fn inst_clobbers(&self, insn: Inst) -> PRegSet {
        self.clobbers[insn.index()]
    }

    fn num_vregs(&self) -> usize {
        self.num_vregs
    }

    fn spillslot_size(&self, _regclass: RegClass) -> usize {
        // Each spill slot = 1 unit = 8 bytes (one u64).
        1
    }
}

/// Build the `MachineEnv` describing available AArch64 registers.
///
/// Allocatable: x0–x14 (15 registers).
/// Scratch (for move resolution): x15.
/// Reserved: x16–x17 (IP0/IP1), x18 (platform), x19 (unused),
/// x20 (stack base), x21 (fuel), x22 (jump table), x29 (fp),
/// x30 (lr), sp.
pub fn build_machine_env() -> MachineEnv {
    let int = RegClass::Int;

    // Preferred: x9–x14 (wasm scratch registers, already used in
    // the current allocator — keeps the calling convention simple).
    let preferred: Vec<PReg> = (9..15).map(|i| PReg::new(i, int)).collect();

    // Non-preferred: x0–x8 (available between wasm calls, but
    // overlap with native ABI argument registers).
    let non_preferred: Vec<PReg> = (0..9).map(|i| PReg::new(i, int)).collect();

    MachineEnv {
        preferred_regs_by_class: [preferred, vec![], vec![]],
        non_preferred_regs_by_class: [non_preferred, vec![], vec![]],
        scratch_by_class: [Some(PReg::new(15, int)), None, None],
        fixed_stack_slots: vec![],
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cfg::build_cfg;
    use crate::ir::{IrFunction, IrInst, Label, VReg as IrVReg};
    use regalloc2::Function;

    fn v(n: u32) -> IrVReg {
        IrVReg(n)
    }
    fn l(n: u32) -> Label {
        Label(n)
    }

    /// Build an IrFunction with the given instructions (minimal metadata).
    fn make_ir(insts: Vec<IrInst>, param_count: u32, total_local_count: u32) -> IrFunction {
        let source_ops = vec![0; insts.len()];
        IrFunction {
            insts,
            source_ops,
            param_count,
            total_local_count,
            max_operand_depth: 0,
            result_count: 1,
        }
    }

    #[test]
    fn adapter_linear_function() {
        let ir = make_ir(
            vec![
                IrInst::IConst { dst: v(0), val: 42 },
                IrInst::Return {
                    results: vec![v(0)],
                },
            ],
            0,
            0,
        );

        let cfg = build_cfg(&ir.insts);
        let adapter = RegAllocAdapter::new(&cfg);

        assert_eq!(adapter.num_insts(), 2);
        assert_eq!(adapter.num_blocks(), 1);
        assert_eq!(adapter.num_vregs(), 1);

        // Instruction 0: IConst — one def
        assert_eq!(adapter.inst_operands(Inst::new(0)).len(), 1);
        // Instruction 1: Return — one fixed use (x9)
        assert_eq!(adapter.inst_operands(Inst::new(1)).len(), 1);
        assert!(adapter.is_ret(Inst::new(1)));
        assert!(adapter.is_branch(Inst::new(1)));
    }

    #[test]
    fn regalloc2_runs_on_linear_function() {
        let ir = make_ir(
            vec![
                IrInst::IConst { dst: v(0), val: 42 },
                IrInst::Return {
                    results: vec![v(0)],
                },
            ],
            0,
            0,
        );

        let cfg = build_cfg(&ir.insts);
        let adapter = RegAllocAdapter::new(&cfg);
        let env = build_machine_env();
        let opts = regalloc2::RegallocOptions {
            validate_ssa: true,
            ..Default::default()
        };

        let output = regalloc2::run(&adapter, &env, &opts).expect("regalloc2 should succeed");
        // Should have allocations for both instructions.
        assert!(!output.allocs.is_empty());
        assert_eq!(output.inst_allocs(Inst::new(0)).len(), 1);
        assert_eq!(output.inst_allocs(Inst::new(1)).len(), 1);
    }

    #[test]
    fn regalloc2_runs_on_if_else() {
        // Simple if/else: if (param == 0) return 1 else return 2
        let ir = make_ir(
            vec![
                // Load param, compare with 0
                IrInst::LocalGet { dst: v(0), idx: 0 },
                IrInst::IConst { dst: v(1), val: 0 },
                IrInst::Cmp {
                    dst: v(2),
                    lhs: v(0),
                    rhs: v(1),
                    cond: crate::ir::IrCond::Eq,
                },
                IrInst::BrIfZero {
                    cond: v(2),
                    label: l(0),
                },
                // Then: store 1
                IrInst::IConst { dst: v(3), val: 1 },
                IrInst::FrameStore { slot: 1, src: v(3) },
                IrInst::Br { label: l(1) },
                // Else: store 2
                IrInst::DefLabel { label: l(0) },
                IrInst::IConst { dst: v(4), val: 2 },
                IrInst::FrameStore { slot: 1, src: v(4) },
                IrInst::Br { label: l(1) },
                // Merge
                IrInst::DefLabel { label: l(1) },
                IrInst::FrameLoad { dst: v(5), slot: 1 },
                IrInst::Return {
                    results: vec![v(5)],
                },
            ],
            1,
            1,
        );

        let cfg = build_cfg(&ir.insts);
        let adapter = RegAllocAdapter::new(&cfg);
        let env = build_machine_env();
        let opts = regalloc2::RegallocOptions {
            validate_ssa: true,
            ..Default::default()
        };

        let output = regalloc2::run(&adapter, &env, &opts).expect("regalloc2 should succeed");
        assert!(!output.allocs.is_empty());
    }

    #[test]
    fn regalloc2_runs_on_call() {
        // Call func 0 with one arg, return result.
        let ir = make_ir(
            vec![
                IrInst::LocalGet { dst: v(0), idx: 0 },
                IrInst::Call {
                    func_idx: 0,
                    args: vec![v(0)],
                    result: Some(v(1)),
                    frame_advance: 32,
                },
                IrInst::Return {
                    results: vec![v(1)],
                },
            ],
            1,
            1,
        );

        let cfg = build_cfg(&ir.insts);
        let adapter = RegAllocAdapter::new(&cfg);
        let env = build_machine_env();
        let opts = regalloc2::RegallocOptions {
            validate_ssa: true,
            ..Default::default()
        };

        let output = regalloc2::run(&adapter, &env, &opts).expect("regalloc2 should succeed");
        // Call has 2 operands (1 arg use + 1 result def).
        assert_eq!(output.inst_allocs(Inst::new(1)).len(), 2);
    }

    #[test]
    fn regalloc2_runs_on_fib_with_fuel() {
        // Reproduces the fib IR with coalesced fuel checks.
        let ir = make_ir(
            vec![
                // Block 0: compare + conditional branch
                IrInst::LocalGet { dst: v(0), idx: 0 },
                IrInst::IConst { dst: v(1), val: 1 },
                IrInst::Cmp {
                    dst: v(2),
                    lhs: v(0),
                    rhs: v(1),
                    cond: crate::ir::IrCond::LeS,
                },
                IrInst::BrIfZero {
                    cond: v(2),
                    label: l(0),
                },
                // Block 1: then — return local
                IrInst::LocalGet { dst: v(3), idx: 0 },
                IrInst::FrameStore { slot: 1, src: v(3) },
                IrInst::FuelConsume { cost: 5 }, IrInst::FuelCheck,
                IrInst::Br { label: l(1) },
                // Block 2 (L0): else — recursive calls
                IrInst::DefLabel { label: l(0) },
                IrInst::LocalGet { dst: v(4), idx: 0 },
                IrInst::IConst { dst: v(5), val: 1 },
                IrInst::Sub {
                    dst: v(6),
                    lhs: v(4),
                    rhs: v(5),
                },
                IrInst::FuelConsume { cost: 3 }, IrInst::FuelCheck,
                IrInst::Call {
                    func_idx: 0,
                    args: vec![v(6)],
                    result: Some(v(7)),
                    frame_advance: 48,
                },
                IrInst::FrameStore { slot: 1, src: v(7) },
                IrInst::FuelConsume { cost: 2 }, IrInst::FuelCheck,
                IrInst::FrameLoad { dst: v(8), slot: 1 },
                IrInst::FrameStore { slot: 1, src: v(8) },
                // Block 3 (L1): merge
                IrInst::DefLabel { label: l(1) },
                IrInst::FrameLoad { dst: v(9), slot: 1 },
                IrInst::Return {
                    results: vec![v(9)],
                },
            ],
            1,
            3,
        );

        let cfg = build_cfg(&ir.insts);
        let adapter = RegAllocAdapter::new(&cfg);
        let env = build_machine_env();
        let opts = regalloc2::RegallocOptions {
            validate_ssa: true,
            ..Default::default()
        };

        let output = regalloc2::run(&adapter, &env, &opts).expect("regalloc2 should succeed on fib with fuel");
        assert!(!output.allocs.is_empty());
    }
}
