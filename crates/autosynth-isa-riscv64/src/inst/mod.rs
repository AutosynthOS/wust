mod add;
mod addi;
mod addiw;
mod addw;
mod beq;
mod bge;
mod bgeu;
mod blt;
mod bltu;
mod bne;
mod jal;
mod jalr;
mod ld;
mod lui;
mod lw;
mod or;
mod sd;
mod slt;
mod sltu;
mod sub;
mod subw;
mod sw;

pub use add::Add;
pub use addi::Addi;
pub use addiw::Addiw;
pub use addw::Addw;
pub use beq::Beq;
pub use bge::Bge;
pub use bgeu::Bgeu;
pub use blt::Blt;
pub use bltu::Bltu;
pub use bne::Bne;
pub use jal::Jal;
pub use jalr::Jalr;
pub use ld::Ld;
pub use lui::Lui;
pub use lw::Lw;
pub use or::Or;
pub use sd::Sd;
pub use slt::Slt;
pub use sltu::Sltu;
pub use sub::Sub;
pub use subw::Subw;
pub use sw::Sw;

use autosynth_isa::{EncodeError, Instruction};

/// RISC-V 64-bit specific: return the 32-bit instruction word.
pub trait Rv64Inst {
    fn encode_word(&self) -> u32;
}

/// Wrapper that bridges `Rv64Inst` to the generic `Instruction` trait.
#[derive(Debug, Clone, Copy)]
pub struct Rv64Instruction<T: Rv64Inst>(pub T);

impl<T: Rv64Inst> Instruction for Rv64Instruction<T> {
    fn encode(&self, buf: &mut [u8]) -> Result<usize, EncodeError> {
        if buf.len() < 4 {
            return Err(EncodeError);
        }
        let w = self.0.encode_word();
        buf[..4].copy_from_slice(&w.to_le_bytes());
        Ok(4)
    }
}

impl<T: Rv64Inst> From<T> for Rv64Instruction<T> {
    fn from(inst: T) -> Self {
        Rv64Instruction(inst)
    }
}
