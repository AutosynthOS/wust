//! Lowering context and operand resolution.
//!
//! This crate bridges the IR and the backend. It provides:
//! - [`LowerCtx`] — the context trait that the orchestrator implements
//! - Operand resolution functions that query the context to fold
//!   immediates or allocate physical registers

use autosynth_ir::{Operand, Register, VReg};
use autosynth_isa::{PReg, PRegOr, Width};

/// The context a lowerer uses to resolve operands and emit code.
///
/// Implemented by the orchestrator/compiler. The backend calls operand
/// resolution methods which delegate to this trait — it never touches
/// virtual registers, the register cache, or spill logic directly.
pub trait LowerCtx {
    /// Get the constant value behind a virtual register, if known.
    ///
    /// Returns `None` if the vreg is not a compile-time constant.
    fn const_value(&self, vreg: VReg) -> Option<i64>;

    /// Force a constant into a physical register via materialization
    /// (e.g. `movz`/`movk`). Returns the register and its width.
    fn materialize_const(&mut self, val: i64, width: Width) -> (PReg, Width);

    /// Resolve a virtual register to a physical register.
    /// Returns the register and its width (from the vreg definition).
    fn resolve_vreg(&mut self, vreg: VReg) -> (PReg, Width);

    /// Allocate a physical register for a definition (output).
    /// Returns the register and its width (from the vreg definition).
    fn define_vreg(&mut self, vreg: VReg) -> (PReg, Width);
}

/// Try to fold an operand as an immediate of type `Imm`, falling back
/// to a physical register if the constant doesn't fit or the operand
/// isn't a constant.
///
/// # Examples
///
/// ```ignore
/// let result = try_imm_or_preg::<UImm12>(&operand, &mut ctx);
/// match result {
///     PRegOr::Imm(imm) => { /* emit immediate form */ }
///     PRegOr::PReg(reg) => { /* emit register form */ }
/// }
/// ```
pub fn try_imm_or_preg<Imm>(operand: &Operand, ctx: &mut impl LowerCtx) -> PRegOr<Imm>
where
    Imm: TryFrom<i64>,
{
    match *operand {
        Operand::Imm32(val) => match Imm::try_from(val as i64) {
            Ok(imm) => PRegOr::Imm(imm),
            Err(_) => {
                let (preg, _) = ctx.materialize_const(val as i64, Width::W32);
                PRegOr::PReg(preg)
            }
        },
        Operand::Imm64(val) => match Imm::try_from(val) {
            Ok(imm) => PRegOr::Imm(imm),
            Err(_) => {
                let (preg, _) = ctx.materialize_const(val, Width::W64);
                PRegOr::PReg(preg)
            }
        },
        Operand::VReg(vreg, _) => {
            // Check if the vreg is a known constant that fits.
            if let Some(val) = ctx.const_value(vreg) {
                if let Ok(imm) = Imm::try_from(val) {
                    return PRegOr::Imm(imm);
                }
            }
            let (preg, _) = ctx.resolve_vreg(vreg);
            PRegOr::PReg(preg)
        }
        Operand::PReg(preg, _) => PRegOr::PReg(preg),
    }
}

/// Force an operand into a physical register, returning its width.
pub fn into_preg(operand: &Operand, ctx: &mut impl LowerCtx) -> (PReg, Width) {
    match *operand {
        Operand::Imm32(val) => ctx.materialize_const(val as i64, Width::W32),
        Operand::Imm64(val) => ctx.materialize_const(val, Width::W64),
        Operand::VReg(vreg, _) => ctx.resolve_vreg(vreg),
        Operand::PReg(preg, w) => (preg, w),
    }
}

/// Resolve a register (virtual or physical) to a physical register,
/// returning its width.
pub fn resolve_register(reg: &Register, ctx: &mut impl LowerCtx) -> (PReg, Width) {
    match *reg {
        Register::VReg(vreg, _) => ctx.resolve_vreg(vreg),
        Register::PReg(preg, w) => (preg, w),
    }
}

/// Allocate a physical register for a register definition, returning
/// its width.
pub fn define_register(reg: &Register, ctx: &mut impl LowerCtx) -> (PReg, Width) {
    match *reg {
        Register::VReg(vreg, _) => ctx.define_vreg(vreg),
        Register::PReg(preg, w) => (preg, w),
    }
}
