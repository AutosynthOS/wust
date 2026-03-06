pub mod backend;
mod builder;
mod disasm;
pub mod ir;
mod regalloc;

#[cfg(test)]
mod tests;

pub use builder::{CodeBuilder, FunctionBuilder, VStack};
pub use ir::{IrType, Register, VReg, VStackId, Value};
pub use ir::block::BlockId;
pub use ir::function::{FunctionIdx, IsaReg};
pub use ir::instruction::{AluOp, CmpOp, IrInst};
