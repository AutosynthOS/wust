#![no_std]

pub mod cond;
pub mod encode;
pub mod imm;
pub mod inst;
pub mod reg;

#[cfg(test)]
mod tests;

pub use cond::Cond;
pub use imm::{Imm32, Imm8, ImmOutOfRange};
pub use inst::{
    AddRegReg, CallRel32, CmpRegImm, Jcc, MovLoad, MovRegImm, MovRegReg, MovStore, Pop, Push,
    Ret, SubRegImm, SubRegReg, X86_64Inst, X86_64Instruction,
};
pub use reg::{Gpr, Gpr32, Gpr64, GprId};
