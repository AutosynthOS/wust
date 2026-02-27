/// Virtual register index — represents an SSA value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VReg(pub u32);

/// Branch target label.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Label(pub u32);

/// Comparison condition for `IrInst::Cmp`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IrCond {
    Eq,
    LeS,
}

/// A single IR instruction using virtual registers.
#[derive(Debug, Clone)]
pub enum IrInst {
    /// Load a constant into a virtual register.
    IConst { dst: VReg, val: i64 },
    /// Define a VReg as holding a function parameter. The value is
    /// already in the param register (x9+idx) from the calling convention.
    /// The lowerer emits nothing — it just tells regalloc2 where the value is.
    ParamDef { dst: VReg, idx: u32 },
    /// Load a local variable into a virtual register.
    LocalGet { dst: VReg, idx: u32 },
    /// Store a virtual register into a local variable.
    LocalSet { idx: u32, src: VReg },
    /// 32-bit integer addition.
    Add { dst: VReg, lhs: VReg, rhs: VReg },
    /// 32-bit integer subtraction.
    Sub { dst: VReg, lhs: VReg, rhs: VReg },
    /// 32-bit add with 12-bit unsigned immediate (0..4095).
    AddImm { dst: VReg, lhs: VReg, imm: u16 },
    /// 32-bit sub with 12-bit unsigned immediate (0..4095).
    SubImm { dst: VReg, lhs: VReg, imm: u16 },
    /// Compare two values, store boolean result (0 or 1).
    Cmp { dst: VReg, lhs: VReg, rhs: VReg, cond: IrCond },
    /// Compare a value with a 12-bit unsigned immediate (0..4095).
    CmpImm { dst: VReg, lhs: VReg, imm: u16, cond: IrCond },
    /// Define a branch target label.
    DefLabel { label: Label },
    /// Unconditional branch.
    Br { label: Label },
    /// Branch if the condition register is zero.
    BrIfZero { cond: VReg, label: Label },
    /// Branch if the condition register is nonzero.
    BrIfNonZero { cond: VReg, label: Label },
    /// Store a value to a frame slot: `[x29 + slot * 8]`.
    ///
    /// Slots 0..total_local_count are locals. Slots beyond that are
    /// operand stack spill slots at control flow merge points.
    FrameStore { slot: u32, src: VReg },
    /// Load a value from a frame slot: `[x29 + slot * 8]`.
    FrameLoad { dst: VReg, slot: u32 },
    /// Call a function by index with register-passed arguments.
    ///
    /// Arguments are passed in x9, x10, ... (scratch registers).
    /// A single result (if any) is returned in x9.
    ///
    /// `frame_advance` is the byte offset to advance x29 before the
    /// call: `(2 + total_local_count + spill_count) * 8`. This is a
    /// per-call-site constant — different call sites may have
    /// different operand stack depths.
    Call {
        func_idx: u32,
        args: Vec<VReg>,
        result: Option<VReg>,
        frame_advance: u32,
    },
    /// Return from the function with the given result values.
    Return { results: Vec<VReg> },
    /// Decrement fuel counter by `cost`. No suspend point — fuel can go
    /// negative between checkpoints.
    FuelConsume { cost: u32 },
    /// Check if fuel is exhausted (negative); suspend if so. The frame
    /// must be canonical before this instruction. When preceded by
    /// `FuelConsume`, the lowerer fuses them into `subs + b.le`.
    FuelCheck,
    /// Trap (unreachable instruction).
    Trap,
}

impl IrInst {
    /// Call `f` for every VReg that is *defined* by this instruction.
    pub fn for_each_def(&self, mut f: impl FnMut(VReg)) {
        match self {
            IrInst::IConst { dst, .. }
            | IrInst::ParamDef { dst, .. }
            | IrInst::LocalGet { dst, .. }
            | IrInst::Add { dst, .. }
            | IrInst::Sub { dst, .. }
            | IrInst::AddImm { dst, .. }
            | IrInst::SubImm { dst, .. }
            | IrInst::Cmp { dst, .. }
            | IrInst::CmpImm { dst, .. }
            | IrInst::FrameLoad { dst, .. } => f(*dst),
            IrInst::Call { result, .. } => {
                if let Some(r) = result {
                    f(*r);
                }
            }
            _ => {}
        }
    }

    /// Call `f` for every VReg that is *read* by this instruction.
    pub fn for_each_use(&self, mut f: impl FnMut(VReg)) {
        match self {
            IrInst::Add { lhs, rhs, .. }
            | IrInst::Sub { lhs, rhs, .. }
            | IrInst::Cmp { lhs, rhs, .. } => {
                f(*lhs);
                f(*rhs);
            }
            IrInst::AddImm { lhs, .. }
            | IrInst::SubImm { lhs, .. }
            | IrInst::CmpImm { lhs, .. } => f(*lhs),
            IrInst::LocalSet { src, .. } | IrInst::FrameStore { src, .. } => f(*src),
            IrInst::BrIfZero { cond, .. } | IrInst::BrIfNonZero { cond, .. } => f(*cond),
            IrInst::Call { args, .. } => {
                for a in args {
                    f(*a);
                }
            }
            IrInst::Return { results } => {
                for r in results {
                    f(*r);
                }
            }
            _ => {}
        }
    }
}

/// A compiled IR function — the output of the wasm-to-IR compiler.
pub struct IrFunction {
    /// The IR instruction sequence.
    pub insts: Vec<IrInst>,
    /// For each IR instruction, the index of the parsed wasm op it
    /// came from. Same length as `insts`. Used by the inspector to
    /// group machine instructions by their source wasm operation.
    pub source_ops: Vec<u32>,
    /// Number of function parameters.
    pub param_count: u32,
    /// Total number of locals (params + declared locals).
    pub total_local_count: u32,
    /// Maximum operand stack depth during execution.
    pub max_operand_depth: u32,
    /// Number of result values.
    pub result_count: u32,
}

impl IrFunction {
    /// Maximum frame size in bytes (for stack bounds checking).
    ///
    /// Layout: [prev_fp][header][locals][operand stack spills]
    /// Each slot is 8 bytes. prev_fp and header are 2 slots (16 bytes).
    pub fn frame_size(&self) -> u32 {
        (2 + self.total_local_count + self.max_operand_depth) * 8
    }
}

impl std::fmt::Display for IrCond {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IrCond::Eq => write!(f, "i32.eq"),
            IrCond::LeS => write!(f, "i32.le_s"),
        }
    }
}

impl std::fmt::Display for VReg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "v{}", self.0)
    }
}

impl std::fmt::Display for Label {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "L{}", self.0)
    }
}

impl std::fmt::Display for IrInst {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IrInst::IConst { dst, val } => write!(f, "  {dst} = i32.const {val}"),
            IrInst::ParamDef { dst, idx } => write!(f, "  {dst} = param {idx}"),
            IrInst::LocalGet { dst, idx } => write!(f, "  {dst} = local.get {idx}"),
            IrInst::LocalSet { idx, src } => write!(f, "  local.set {idx}, {src}"),
            IrInst::Add { dst, lhs, rhs } => write!(f, "  {dst} = i32.add {lhs}, {rhs}"),
            IrInst::Sub { dst, lhs, rhs } => write!(f, "  {dst} = i32.sub {lhs}, {rhs}"),
            IrInst::AddImm { dst, lhs, imm } => write!(f, "  {dst} = i32.add {lhs}, #{imm}"),
            IrInst::SubImm { dst, lhs, imm } => write!(f, "  {dst} = i32.sub {lhs}, #{imm}"),
            IrInst::Cmp { dst, lhs, rhs, cond } => {
                write!(f, "  {dst} = {cond} {lhs}, {rhs}")
            }
            IrInst::CmpImm { dst, lhs, imm, cond } => {
                write!(f, "  {dst} = {cond} {lhs}, #{imm}")
            }
            IrInst::DefLabel { label } => write!(f, "{label}:"),
            IrInst::Br { label } => write!(f, "  br {label}"),
            IrInst::BrIfZero { cond, label } => write!(f, "  br_if_zero {cond}, {label}"),
            IrInst::BrIfNonZero { cond, label } => {
                write!(f, "  br_if_nz {cond}, {label}")
            }
            IrInst::FrameStore { slot, src } => write!(f, "  frame[{slot}] = {src}"),
            IrInst::FrameLoad { dst, slot } => write!(f, "  {dst} = frame[{slot}]"),
            IrInst::Call {
                func_idx,
                args,
                result,
                ..
            } => {
                if let Some(r) = result {
                    write!(f, "  {r} = call {func_idx}")?;
                } else {
                    write!(f, "  call {func_idx}")?;
                }
                if !args.is_empty() {
                    write!(f, "(")?;
                    for (i, a) in args.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{a}")?;
                    }
                    write!(f, ")")?;
                }
                Ok(())
            }
            IrInst::Return { results } => {
                write!(f, "  return")?;
                for (i, r) in results.iter().enumerate() {
                    if i == 0 {
                        write!(f, " {r}")?;
                    } else {
                        write!(f, ", {r}")?;
                    }
                }
                Ok(())
            }
            IrInst::FuelConsume { cost } => write!(f, "  fuel_consume {cost}"),
            IrInst::FuelCheck => write!(f, "  fuel_check"),
            IrInst::Trap => write!(f, "  trap"),
        }
    }
}

impl std::fmt::Display for IrFunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "fn(params={}, locals={}, max_depth={}, results={}, frame={}B):",
            self.param_count,
            self.total_local_count,
            self.max_operand_depth,
            self.result_count,
            self.frame_size()
        )?;
        for inst in &self.insts {
            writeln!(f, "{inst}")?;
        }
        Ok(())
    }
}
