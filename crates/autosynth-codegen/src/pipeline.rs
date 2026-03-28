use std::collections::BTreeMap;

use autosynth_ir::{BlockId, Operand};
use autosynth_isa::PReg;
use autosynth_regalloc::{RegAlloc, VInit};
use autosynth_selector::{CodeCtx, Selector, SelectorError};

use crate::ir::IrFunction;

/// A compiled function — lowered VCode blocks + regalloc state.
pub struct VCodeFunction {
    pub regalloc: RegAlloc,
    pub blocks: BTreeMap<BlockId, CodeCtx>,
    pub block_order: Vec<BlockId>,
}

/// Compile an IR function through a selector.
///
/// Takes ownership of the IrFunction. Walks blocks in layout order,
/// runs the selector on each block, and collects the lowered output.
pub fn compile(
    func: IrFunction,
    selector: &mut impl Selector,
) -> Result<VCodeFunction, SelectorError> {
    let IrFunction { mut regalloc, blocks: ir_blocks, block_order } = func;
    let mut blocks = BTreeMap::new();

    for &block_id in &block_order {
        let block = &ir_blocks[&block_id];
        let mut input = CodeCtx::from(
            block.instructions.clone(),
            block.operands.clone(),
        );
        let mut output = CodeCtx::new();

        selector.select(&mut regalloc, &mut input, &mut output)?;

        blocks.insert(block_id, output);
    }

    Ok(VCodeFunction { regalloc, blocks, block_order })
}

/// Trivial register allocation — resolves VRegs to PRegs in-place.
///
/// - PReg(p) → Operand::PReg(p)
/// - InstDst → same PReg as the first input operand
/// - Already-resolved operands (UImm12 etc.) → unchanged
///
/// Placeholder — a real regalloc would do liveness, spilling, etc.
pub fn trivial_regalloc(func: &mut VCodeFunction) {
    let regalloc = &func.regalloc;
    for block in func.blocks.values_mut() {
        let mut last_preg: Option<PReg> = None;
        for op in &mut block.operands {
            *op = resolve_operand(regalloc, *op, &mut last_preg);
        }
    }
}

fn resolve_operand(regalloc: &RegAlloc, op: Operand, last_preg: &mut Option<PReg>) -> Operand {
    match op {
        Operand::VReg(id) => match regalloc.init(id) {
            VInit::PReg(preg) => {
                *last_preg = Some(*preg);
                Operand::PReg(*preg)
            }
            VInit::InstDst => {
                let preg = last_preg.expect("InstDst with no prior PReg");
                Operand::PReg(preg)
            }
            _ => op,
        },
        other => {
            if let Operand::PReg(preg) = &other {
                *last_preg = Some(*preg);
            }
            other
        }
    }
}
