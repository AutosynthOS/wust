/// AArch64 instruction selector.
///
/// Transforms high-level VCode + VReg operands into lower-level VCode
/// with resolved operands (immediates, physical registers). Handles:
///
/// - Operand resolution: Const → Imm12 or materialization sequence
/// - Pattern matching: Comp + BrIf → fused compare-and-branch
/// - ABI: call setup, frame advance/restore
///
/// Does NOT handle register allocation — that runs as a separate pass
/// on the complete VCode output.
use autosynth_ir::{AluOp, BlockId, CompOp, Operand, VCode, VRegId};
use autosynth_isa::Width;
