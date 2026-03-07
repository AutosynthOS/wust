#![no_std]

pub mod imm;
pub mod inst;
pub mod reg;

#[cfg(test)]
mod tests;

pub use imm::{BImm13, ImmOutOfRange, JImm21, SImm12, SImm20};
pub use inst::{
    Add, Addi, Addiw, Addw, Beq, Bge, Bgeu, Blt, Bltu, Bne, Jal, Jalr, Ld, Lui, Lw, Or,
    Rv64Inst, Rv64Instruction, Sd, Slt, Sltu, Sub, Subw, Sw,
};
pub use reg::{Gpr, GprId};
