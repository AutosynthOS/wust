#![no_std]

pub mod cond;
pub mod imm;
pub mod inst;
pub mod reg;

#[cfg(test)]
mod tests;

pub use cond::Cond;
pub use imm::{ImmOutOfRange, SImm9, UImm12, UImm16};
pub use inst::{
    Aarch64Inst, Aarch64Instruction, InstAdapter, AddImm, AddReg, BCond, Bl, LdrPost, LdrUoff,
    Movk, Movz, OrrReg, Ret, StrPre, StrUoff, SubImm, SubReg, SubsImm, SubsReg,
};
pub use reg::{Gpr, GprId, GprOrSp, GprOrZr, WGpr, XGpr};
