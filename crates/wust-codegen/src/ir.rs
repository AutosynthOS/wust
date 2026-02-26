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
    /// Load a local variable into a virtual register.
    LocalGet { dst: VReg, idx: u32 },
    /// Store a virtual register into a local variable.
    LocalSet { idx: u32, src: VReg },
    /// 32-bit integer addition.
    Add { dst: VReg, lhs: VReg, rhs: VReg },
    /// 32-bit integer subtraction.
    Sub { dst: VReg, lhs: VReg, rhs: VReg },
    /// Compare two values, store boolean result (0 or 1).
    Cmp { dst: VReg, lhs: VReg, rhs: VReg, cond: IrCond },
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
    /// Decrement fuel counter by `cost`; yield if exhausted.
    FuelCheck { cost: u32 },
    /// Trap (unreachable instruction).
    Trap,
}

/// A compiled IR function — the output of the wasm-to-IR compiler.
pub struct IrFunction {
    /// The IR instruction sequence.
    pub insts: Vec<IrInst>,
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
            IrInst::LocalGet { dst, idx } => write!(f, "  {dst} = local.get {idx}"),
            IrInst::LocalSet { idx, src } => write!(f, "  local.set {idx}, {src}"),
            IrInst::Add { dst, lhs, rhs } => write!(f, "  {dst} = i32.add {lhs}, {rhs}"),
            IrInst::Sub { dst, lhs, rhs } => write!(f, "  {dst} = i32.sub {lhs}, {rhs}"),
            IrInst::Cmp { dst, lhs, rhs, cond } => {
                write!(f, "  {dst} = {cond} {lhs}, {rhs}")
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
            IrInst::FuelCheck { cost } => write!(f, "  fuel_check {cost}"),
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
