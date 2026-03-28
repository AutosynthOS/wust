/// AArch64 instruction selector.
///
/// Transforms high-level VCode + VReg operands into lower-level VCode
/// with resolved operands (immediates, physical registers).
use autosynth_ir::{AluOp, Operand, VCode, VRegId};
use autosynth_isa::UImm12;
use autosynth_regalloc::{RegAlloc, VInit};
use autosynth_selector::{CodeCtx, Selector, SelectorError};

pub struct Aarch64Selector<'a> {
    regalloc: &'a RegAlloc,
}

impl<'a> Aarch64Selector<'a> {
    pub fn new(regalloc: &'a RegAlloc) -> Self {
        Self { regalloc }
    }

    /// Try to fold a VReg operand as a UImm12 if it's a small constant.
    /// Returns the original operand unchanged if it can't be folded.
    fn try_fold_uimm12(&self, op: Operand) -> Operand {
        let Operand::VReg { id, .. } = op else {
            return op;
        };
        let VInit::Const(val) = self.regalloc.init(id) else {
            return op;
        };
        match UImm12::try_from(*val) {
            Ok(imm) => Operand::UImm12(imm),
            Err(_) => op,
        }
    }
}

impl Selector for Aarch64Selector<'_> {
    fn select(
        &mut self,
        input: &mut CodeCtx,
        output: &mut CodeCtx,
    ) -> Result<(), SelectorError> {
        let mut ops = input.operands.drain(..).peekable();

        for inst in input.instructions.drain(..) {
            match &inst {
                VCode::Alu { op } => {
                    let lhs = ops.next().ok_or(SelectorError::OperandUnderflow)?;
                    let rhs = ops.next().ok_or(SelectorError::OperandUnderflow)?;
                    let dst = ops.next().ok_or(SelectorError::OperandUnderflow)?;

                    output.push_operand(lhs);
                    output.push_operand(self.try_fold_uimm12(rhs));
                    output.push_operand(dst);
                    output.push_inst(inst);
                }
                _ => {
                    output.push_inst(inst);
                }
            }
        }

        Ok(())
    }
}
