mod add_reg;
mod call_rel;
mod cmp_imm;
mod jcc;
mod mov_imm;
mod mov_load;
mod mov_reg;
mod mov_store;
mod pop;
mod push;
mod ret;
mod sub_imm;
mod sub_reg;

pub use add_reg::AddRegReg;
pub use call_rel::CallRel32;
pub use cmp_imm::CmpRegImm;
pub use jcc::Jcc;
pub use mov_imm::MovRegImm;
pub use mov_load::MovLoad;
pub use mov_reg::MovRegReg;
pub use mov_store::MovStore;
pub use pop::Pop;
pub use push::Push;
pub use ret::Ret;
pub use sub_imm::SubRegImm;
pub use sub_reg::SubRegReg;

use autosynth_isa::{EncodeError, Instruction};

/// x86_64-specific: encode into a byte buffer, return byte count.
pub trait X86_64Inst {
    /// Encode the instruction into `buf`, returning the number of bytes written.
    ///
    /// The caller must ensure `buf` has at least 15 bytes available
    /// (the maximum x86_64 instruction length).
    fn encode_bytes(&self, buf: &mut [u8]) -> usize;
}

/// Wrapper that bridges `X86_64Inst` to the generic `Instruction` trait.
#[derive(Debug, Clone, Copy)]
pub struct X86_64Instruction<T: X86_64Inst>(pub T);

impl<T: X86_64Inst> Instruction for X86_64Instruction<T> {
    fn encode(&self, buf: &mut [u8]) -> Result<usize, EncodeError> {
        if buf.len() < 15 {
            return Err(EncodeError);
        }
        Ok(self.0.encode_bytes(buf))
    }
}

impl<T: X86_64Inst> From<T> for X86_64Instruction<T> {
    fn from(inst: T) -> Self {
        X86_64Instruction(inst)
    }
}
