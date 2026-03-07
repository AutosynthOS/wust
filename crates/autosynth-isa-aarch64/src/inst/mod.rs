mod add_imm;
mod add_reg;
mod b_cond;
mod bl;
mod ldr_post;
mod ldr_uoff;
mod movz;
mod orr_reg;
mod ret;
mod str_pre;
mod str_uoff;
mod sub_imm;
mod sub_reg;
mod subs_imm;
mod subs_reg;

pub use add_imm::AddImm;
pub use add_reg::AddReg;
pub use b_cond::BCond;
pub use bl::Bl;
pub use ldr_post::LdrPost;
pub use ldr_uoff::LdrUoff;
pub use movz::Movz;
pub use orr_reg::OrrReg;
pub use ret::Ret;
pub use str_pre::StrPre;
pub use str_uoff::StrUoff;
pub use sub_imm::SubImm;
pub use sub_reg::SubReg;
pub use subs_imm::SubsImm;
pub use subs_reg::SubsReg;

use autosynth_isa::{EncodeError, Instruction};

/// Aarch64-specific: just return the 32-bit instruction word.
pub trait Aarch64Inst {
    fn encode_word(&self) -> u32;
}

/// Wrapper that bridges `Aarch64Inst` → `Instruction`.
#[derive(Debug, Clone, Copy)]
pub struct Aarch64Instruction<T: Aarch64Inst>(pub T);

impl<T: Aarch64Inst> Instruction for Aarch64Instruction<T> {
    fn encode(&self, buf: &mut [u8]) -> Result<usize, EncodeError> {
        if buf.len() < 4 {
            return Err(EncodeError);
        }
        let w = self.0.encode_word();
        buf[..4].copy_from_slice(&w.to_le_bytes());
        Ok(4)
    }
}

impl<T: Aarch64Inst> From<T> for Aarch64Instruction<T> {
    fn from(inst: T) -> Self {
        Aarch64Instruction(inst)
    }
}
