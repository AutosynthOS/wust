/// Virtual register index — represents an SSA value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VReg(pub u32);

/// Branch target label.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Label(pub u32);

/// Operand for ALU instructions — either a virtual register or an immediate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Operand {
    Reg(VReg),
    Imm(i64),
}

/// Binary ALU operation type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AluOp {
    // i32 arithmetic
    I32Add, I32Sub, I32Mul, I32DivS, I32DivU, I32RemS, I32RemU,
    // i32 bitwise
    I32And, I32Or, I32Xor, I32Shl, I32ShrS, I32ShrU, I32Rotl, I32Rotr,
    // i32 comparison (result is 0 or 1)
    I32Eq, I32Ne, I32LtS, I32LtU, I32GtS, I32GtU, I32LeS, I32LeU, I32GeS, I32GeU,
    // i64 arithmetic
    I64Add, I64Sub, I64Mul, I64DivS, I64DivU, I64RemS, I64RemU,
    // i64 bitwise
    I64And, I64Or, I64Xor, I64Shl, I64ShrS, I64ShrU, I64Rotl, I64Rotr,
    // i64 comparison (result is 0 or 1)
    I64Eq, I64Ne, I64LtS, I64LtU, I64GtS, I64GtU, I64LeS, I64LeU, I64GeS, I64GeU,
}

/// Unary operation type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    I32Clz, I32Ctz, I32Popcnt, I32Eqz,
    I64Clz, I64Ctz, I64Popcnt, I64Eqz,
    I32WrapI64, I64ExtendI32S, I64ExtendI32U,
    I32Extend8S, I32Extend16S, I64Extend8S, I64Extend16S, I64Extend32S,
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
    /// Binary ALU operation.
    Alu { op: AluOp, dst: VReg, lhs: VReg, rhs: Operand },
    /// Unary operation.
    Unary { op: UnaryOp, dst: VReg, src: VReg },
    /// Define a branch target label with block parameters.
    /// Each param is a fresh VReg defined at block entry.
    DefLabel { label: Label, params: Vec<VReg> },
    /// Unconditional branch with block arguments.
    /// Args are values passed to the target block's params.
    Br { label: Label, args: Vec<VReg> },
    /// Branch if the condition register is zero.
    /// Args are values passed to the target block's params.
    BrIfZero { cond: VReg, label: Label, args: Vec<VReg> },
    /// Branch if the condition register is nonzero.
    /// Args are values passed to the target block's params.
    BrIfNonZero { cond: VReg, label: Label, args: Vec<VReg> },
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
    /// Check if fuel is exhausted (negative); suspend if so.
    /// When preceded by `FuelConsume`, the lowerer fuses them into
    /// `subs + b.le`.
    ///
    /// `live_state` lists (canonical_slot, vreg) pairs for all values
    /// that must be materialized to the frame on the cold suspend path.
    /// On the hot path these VRegs stay in registers; regalloc2 keeps
    /// them live because they appear as uses.
    FuelCheck { live_state: Vec<(u32, VReg)> },
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
            | IrInst::Alu { dst, .. }
            | IrInst::Unary { dst, .. }
            | IrInst::FrameLoad { dst, .. } => f(*dst),
            IrInst::Call { result, .. } => {
                if let Some(r) = result {
                    f(*r);
                }
            }
            IrInst::DefLabel { params, .. } => {
                for p in params {
                    f(*p);
                }
            }
            _ => {}
        }
    }

    /// Call `f` for every VReg that is *read* by this instruction.
    pub fn for_each_use(&self, mut f: impl FnMut(VReg)) {
        match self {
            IrInst::Alu { lhs, rhs, .. } => {
                f(*lhs);
                if let Operand::Reg(r) = rhs {
                    f(*r);
                }
            }
            IrInst::Unary { src, .. } => f(*src),
            IrInst::LocalSet { src, .. } | IrInst::FrameStore { src, .. } => f(*src),
            IrInst::BrIfZero { cond, args, .. } | IrInst::BrIfNonZero { cond, args, .. } => {
                f(*cond);
                for a in args {
                    f(*a);
                }
            }
            IrInst::Br { args, .. } => {
                for a in args {
                    f(*a);
                }
            }
            IrInst::FuelCheck { live_state } => {
                for (_, vreg) in live_state {
                    f(*vreg);
                }
            }
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

impl std::fmt::Display for AluOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name = match self {
            AluOp::I32Add => "i32.add", AluOp::I32Sub => "i32.sub",
            AluOp::I32Mul => "i32.mul", AluOp::I32DivS => "i32.div_s",
            AluOp::I32DivU => "i32.div_u", AluOp::I32RemS => "i32.rem_s",
            AluOp::I32RemU => "i32.rem_u",
            AluOp::I32And => "i32.and", AluOp::I32Or => "i32.or",
            AluOp::I32Xor => "i32.xor", AluOp::I32Shl => "i32.shl",
            AluOp::I32ShrS => "i32.shr_s", AluOp::I32ShrU => "i32.shr_u",
            AluOp::I32Rotl => "i32.rotl", AluOp::I32Rotr => "i32.rotr",
            AluOp::I32Eq => "i32.eq", AluOp::I32Ne => "i32.ne",
            AluOp::I32LtS => "i32.lt_s", AluOp::I32LtU => "i32.lt_u",
            AluOp::I32GtS => "i32.gt_s", AluOp::I32GtU => "i32.gt_u",
            AluOp::I32LeS => "i32.le_s", AluOp::I32LeU => "i32.le_u",
            AluOp::I32GeS => "i32.ge_s", AluOp::I32GeU => "i32.ge_u",
            AluOp::I64Add => "i64.add", AluOp::I64Sub => "i64.sub",
            AluOp::I64Mul => "i64.mul", AluOp::I64DivS => "i64.div_s",
            AluOp::I64DivU => "i64.div_u", AluOp::I64RemS => "i64.rem_s",
            AluOp::I64RemU => "i64.rem_u",
            AluOp::I64And => "i64.and", AluOp::I64Or => "i64.or",
            AluOp::I64Xor => "i64.xor", AluOp::I64Shl => "i64.shl",
            AluOp::I64ShrS => "i64.shr_s", AluOp::I64ShrU => "i64.shr_u",
            AluOp::I64Rotl => "i64.rotl", AluOp::I64Rotr => "i64.rotr",
            AluOp::I64Eq => "i64.eq", AluOp::I64Ne => "i64.ne",
            AluOp::I64LtS => "i64.lt_s", AluOp::I64LtU => "i64.lt_u",
            AluOp::I64GtS => "i64.gt_s", AluOp::I64GtU => "i64.gt_u",
            AluOp::I64LeS => "i64.le_s", AluOp::I64LeU => "i64.le_u",
            AluOp::I64GeS => "i64.ge_s", AluOp::I64GeU => "i64.ge_u",
        };
        write!(f, "{name}")
    }
}

impl std::fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name = match self {
            UnaryOp::I32Clz => "i32.clz", UnaryOp::I32Ctz => "i32.ctz",
            UnaryOp::I32Popcnt => "i32.popcnt", UnaryOp::I32Eqz => "i32.eqz",
            UnaryOp::I64Clz => "i64.clz", UnaryOp::I64Ctz => "i64.ctz",
            UnaryOp::I64Popcnt => "i64.popcnt", UnaryOp::I64Eqz => "i64.eqz",
            UnaryOp::I32WrapI64 => "i32.wrap_i64",
            UnaryOp::I64ExtendI32S => "i64.extend_i32_s",
            UnaryOp::I64ExtendI32U => "i64.extend_i32_u",
            UnaryOp::I32Extend8S => "i32.extend8_s",
            UnaryOp::I32Extend16S => "i32.extend16_s",
            UnaryOp::I64Extend8S => "i64.extend8_s",
            UnaryOp::I64Extend16S => "i64.extend16_s",
            UnaryOp::I64Extend32S => "i64.extend32_s",
        };
        write!(f, "{name}")
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

/// Format a parenthesized argument list for branch instructions.
fn fmt_args(f: &mut std::fmt::Formatter<'_>, args: &[VReg]) -> std::fmt::Result {
    if !args.is_empty() {
        write!(f, "(")?;
        for (i, a) in args.iter().enumerate() {
            if i > 0 { write!(f, ", ")?; }
            write!(f, "{a}")?;
        }
        write!(f, ")")?;
    }
    Ok(())
}

impl std::fmt::Display for IrInst {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IrInst::IConst { dst, val } => write!(f, "  {dst} = i32.const {val}"),
            IrInst::ParamDef { dst, idx } => write!(f, "  {dst} = param {idx}"),
            IrInst::LocalGet { dst, idx } => write!(f, "  {dst} = local.get {idx}"),
            IrInst::LocalSet { idx, src } => write!(f, "  local.set {idx}, {src}"),
            IrInst::Alu { op, dst, lhs, rhs } => {
                match rhs {
                    Operand::Reg(r) => write!(f, "  {dst} = {op} {lhs}, {r}"),
                    Operand::Imm(i) => write!(f, "  {dst} = {op} {lhs}, #{i}"),
                }
            }
            IrInst::Unary { op, dst, src } => write!(f, "  {dst} = {op} {src}"),
            IrInst::DefLabel { label, params } => {
                write!(f, "{label}:")?;
                if !params.is_empty() {
                    write!(f, "(")?;
                    for (i, p) in params.iter().enumerate() {
                        if i > 0 { write!(f, ", ")?; }
                        write!(f, "{p}")?;
                    }
                    write!(f, ")")?;
                }
                Ok(())
            }
            IrInst::Br { label, args } => {
                write!(f, "  br {label}")?;
                fmt_args(f, args)
            }
            IrInst::BrIfZero { cond, label, args } => {
                write!(f, "  br_if_zero {cond}, {label}")?;
                fmt_args(f, args)
            }
            IrInst::BrIfNonZero { cond, label, args } => {
                write!(f, "  br_if_nz {cond}, {label}")?;
                fmt_args(f, args)
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
            IrInst::FuelCheck { live_state } => {
                write!(f, "  fuel_check")?;
                if !live_state.is_empty() {
                    write!(f, " [")?;
                    for (i, (slot, vreg)) in live_state.iter().enumerate() {
                        if i > 0 { write!(f, ", ")?; }
                        write!(f, "frame[{slot}]={vreg}")?;
                    }
                    write!(f, "]")?;
                }
                Ok(())
            }
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
