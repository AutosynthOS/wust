mod add_imm;
mod add_reg;
mod b_cond;
mod bl;
mod ldr_post;
mod ldr_uoff;
mod movk;
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
pub use movk::Movk;
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
pub struct InstAdapter<T: Aarch64Inst>(pub T);

impl<T: Aarch64Inst> Instruction for InstAdapter<T> {
    fn encode(&self, buf: &mut [u8]) -> Result<usize, EncodeError> {
        if buf.len() < 4 {
            return Err(EncodeError);
        }
        let w = self.0.encode_word();
        buf[..4].copy_from_slice(&w.to_le_bytes());
        Ok(4)
    }
}

impl<T: Aarch64Inst> From<T> for InstAdapter<T> {
    fn from(inst: T) -> Self {
        InstAdapter(inst)
    }
}

/// Unified enum of all AArch64 instructions.
///
/// Stores the instruction AST without encoding, so it can be
/// re-rendered or inspected after emission.
#[derive(Debug, Clone, Copy)]
pub enum Aarch64Instruction {
    AddImm(AddImm),
    AddReg(AddReg),
    BCond(BCond),
    Bl(Bl),
    LdrPost(LdrPost),
    LdrUoff(LdrUoff),
    Movk(Movk),
    Movz(Movz),
    OrrReg(OrrReg),
    Ret(Ret),
    StrPre(StrPre),
    StrUoff(StrUoff),
    SubImm(SubImm),
    SubReg(SubReg),
    SubsImm(SubsImm),
    SubsReg(SubsReg),
}

impl core::fmt::Display for Aarch64Instruction {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::AddImm(i) => write!(f, "{i}"),
            Self::AddReg(i) => write!(f, "{i}"),
            Self::BCond(i) => write!(f, "{i}"),
            Self::Bl(i) => write!(f, "{i}"),
            Self::LdrPost(i) => write!(f, "{i}"),
            Self::LdrUoff(i) => write!(f, "{i}"),
            Self::Movk(i) => write!(f, "{i}"),
            Self::Movz(i) => write!(f, "{i}"),
            Self::OrrReg(i) => write!(f, "{i}"),
            Self::Ret(i) => write!(f, "{i}"),
            Self::StrPre(i) => write!(f, "{i}"),
            Self::StrUoff(i) => write!(f, "{i}"),
            Self::SubImm(i) => write!(f, "{i}"),
            Self::SubReg(i) => write!(f, "{i}"),
            Self::SubsImm(i) => write!(f, "{i}"),
            Self::SubsReg(i) => write!(f, "{i}"),
        }
    }
}

impl Aarch64Inst for Aarch64Instruction {
    fn encode_word(&self) -> u32 {
        match self {
            Self::AddImm(i) => i.encode_word(),
            Self::AddReg(i) => i.encode_word(),
            Self::BCond(i) => i.encode_word(),
            Self::Bl(i) => i.encode_word(),
            Self::LdrPost(i) => i.encode_word(),
            Self::LdrUoff(i) => i.encode_word(),
            Self::Movk(i) => i.encode_word(),
            Self::Movz(i) => i.encode_word(),
            Self::OrrReg(i) => i.encode_word(),
            Self::Ret(i) => i.encode_word(),
            Self::StrPre(i) => i.encode_word(),
            Self::StrUoff(i) => i.encode_word(),
            Self::SubImm(i) => i.encode_word(),
            Self::SubReg(i) => i.encode_word(),
            Self::SubsImm(i) => i.encode_word(),
            Self::SubsReg(i) => i.encode_word(),
        }
    }
}

macro_rules! impl_from_inst {
    ($($variant:ident($ty:ty)),* $(,)?) => {
        $(
            impl From<$ty> for Aarch64Instruction {
                fn from(inst: $ty) -> Self {
                    Aarch64Instruction::$variant(inst)
                }
            }
        )*
    };
}

impl_from_inst! {
    AddImm(AddImm), AddReg(AddReg), BCond(BCond), Bl(Bl),
    LdrPost(LdrPost), LdrUoff(LdrUoff), Movk(Movk), Movz(Movz), OrrReg(OrrReg),
    Ret(Ret), StrPre(StrPre), StrUoff(StrUoff), SubImm(SubImm),
    SubReg(SubReg), SubsImm(SubsImm), SubsReg(SubsReg),
}
