use wasmparser::{Operator, ValType};

/// Our own instruction enum — decoded from wasmparser's Operator once at parse
/// time so we don't re-parse during execution.
#[derive(Debug, Clone)]
pub enum Instruction {
    // Control
    Unreachable,
    Nop,
    Block { ty: BlockType, end_pc: usize },
    Loop { ty: BlockType },
    If { ty: BlockType, end_pc: usize, else_pc: Option<usize> },
    Else,
    End,
    Br(u32),
    BrIf(u32),
    BrTable { targets: Vec<u32>, default: u32 },
    Return,
    Call(u32),
    CallIndirect { type_idx: u32, table_idx: u32 },
    Drop,
    Select,

    // Locals / Globals
    LocalGet(u32),
    LocalSet(u32),
    LocalTee(u32),
    GlobalGet(u32),
    GlobalSet(u32),

    // Memory (align is a hint per spec — not stored)
    I32Load(u64),
    I64Load(u64),
    F32Load(u64),
    F64Load(u64),
    I32Load8S(u64),
    I32Load8U(u64),
    I32Load16S(u64),
    I32Load16U(u64),
    I64Load8S(u64),
    I64Load8U(u64),
    I64Load16S(u64),
    I64Load16U(u64),
    I64Load32S(u64),
    I64Load32U(u64),
    I32Store(u64),
    I64Store(u64),
    F32Store(u64),
    F64Store(u64),
    I32Store8(u64),
    I32Store16(u64),
    I64Store8(u64),
    I64Store16(u64),
    I64Store32(u64),
    MemorySize,
    MemoryGrow,

    // Constants
    I32Const(i32),
    I64Const(i64),
    F32Const(f32),
    F64Const(f64),

    // Superinstructions (fused sequences for hot paths)
    /// LocalGet(idx) + I32Const(val) — pushes local then constant
    LocalGetI32Const(u32, i32),
    /// LocalGet(a) + LocalGet(b) — pushes two locals
    LocalGetLocalGet(u32, u32),

    // i32 arithmetic
    I32Eqz,
    I32Eq,
    I32Ne,
    I32LtS,
    I32LtU,
    I32GtS,
    I32GtU,
    I32LeS,
    I32LeU,
    I32GeS,
    I32GeU,
    I32Clz,
    I32Ctz,
    I32Popcnt,
    I32Add,
    I32Sub,
    I32Mul,
    I32DivS,
    I32DivU,
    I32RemS,
    I32RemU,
    I32And,
    I32Or,
    I32Xor,
    I32Shl,
    I32ShrS,
    I32ShrU,
    I32Rotl,
    I32Rotr,

    // i64 arithmetic
    I64Eqz,
    I64Eq,
    I64Ne,
    I64LtS,
    I64LtU,
    I64GtS,
    I64GtU,
    I64LeS,
    I64LeU,
    I64GeS,
    I64GeU,
    I64Clz,
    I64Ctz,
    I64Popcnt,
    I64Add,
    I64Sub,
    I64Mul,
    I64DivS,
    I64DivU,
    I64RemS,
    I64RemU,
    I64And,
    I64Or,
    I64Xor,
    I64Shl,
    I64ShrS,
    I64ShrU,
    I64Rotl,
    I64Rotr,

    // Conversions
    I32WrapI64,
    I64ExtendI32S,
    I64ExtendI32U,

    // f32 comparison
    F32Eq,
    F32Ne,
    F32Lt,
    F32Gt,
    F32Le,
    F32Ge,
    F64Eq,
    F64Ne,
    F64Lt,
    F64Gt,
    F64Le,
    F64Ge,
    F32Abs,
    F32Neg,
    F32Ceil,
    F32Floor,
    F32Trunc,
    F32Nearest,
    F32Sqrt,
    F32Add,
    F32Sub,
    F32Mul,
    F32Div,
    F32Min,
    F32Max,
    F32Copysign,
    F64Abs,
    F64Neg,
    F64Ceil,
    F64Floor,
    F64Trunc,
    F64Nearest,
    F64Sqrt,
    F64Add,
    F64Sub,
    F64Mul,
    F64Div,
    F64Min,
    F64Max,
    F64Copysign,

    // More conversions
    I32TruncF32S,
    I32TruncF32U,
    I32TruncF64S,
    I32TruncF64U,
    I64TruncF32S,
    I64TruncF32U,
    I64TruncF64S,
    I64TruncF64U,
    F32ConvertI32S,
    F32ConvertI32U,
    F32ConvertI64S,
    F32ConvertI64U,
    F32DemoteF64,
    F64ConvertI32S,
    F64ConvertI32U,
    F64ConvertI64S,
    F64ConvertI64U,
    F64PromoteF32,
    I32ReinterpretF32,
    I64ReinterpretF64,
    F32ReinterpretI32,
    F64ReinterpretI64,

    // Sign extension
    I32Extend8S,
    I32Extend16S,
    I64Extend8S,
    I64Extend16S,
    I64Extend32S,

    // Reference types
    RefFunc(u32),
    RefNull,

    // Reference type check
    RefIsNull,

    // Bulk memory operations
    TableInit { elem_idx: u32, table_idx: u32 },
    ElemDrop(u32),
    MemoryInit(u32),    // data segment index
    DataDrop(u32),      // data segment index
    MemoryCopy,
    MemoryFill,

    // Table operations
    TableGet(u32),      // table index
    TableSet(u32),      // table index
    TableGrow(u32),     // table index
    TableSize(u32),     // table index
    TableCopy { dst_table: u32, src_table: u32 },
    TableFill(u32),     // table index

    // Saturating truncation
    I32TruncSatF32S,
    I32TruncSatF32U,
    I32TruncSatF64S,
    I32TruncSatF64U,
    I64TruncSatF32S,
    I64TruncSatF32U,
    I64TruncSatF64S,
    I64TruncSatF64U,
}

#[derive(Debug, Clone)]
pub enum BlockType {
    Empty,
    Val(ValType),
    FuncType(u32),
}

/// Fill in end_pc/else_pc for Block and If instructions.
pub fn resolve_block_targets(body: &mut [Instruction]) {
    // Stack of (block_start_pc, is_if)
    let mut stack: Vec<(usize, bool)> = Vec::new();
    let mut else_map: Vec<(usize, usize)> = Vec::new(); // (if_pc, else_pc)

    for i in 0..body.len() {
        match &body[i] {
            Instruction::Block { .. } => stack.push((i, false)),
            Instruction::Loop { .. } => stack.push((i, false)),
            Instruction::If { .. } => stack.push((i, true)),
            Instruction::Else => {
                // Record the else position for the most recent If
                if let Some(&(if_pc, true)) = stack.last() {
                    else_map.push((if_pc, i));
                }
            }
            Instruction::End => {
                if let Some((start_pc, is_if)) = stack.pop() {
                    match &body[start_pc] {
                        Instruction::Block { .. } | Instruction::If { .. } => {
                            let else_pc = if is_if {
                                else_map.iter().rev()
                                    .find(|(ip, _)| *ip == start_pc)
                                    .map(|(_, ep)| *ep)
                            } else {
                                None
                            };
                            // Patch the instruction
                            match &mut body[start_pc] {
                                Instruction::Block { end_pc, .. } => *end_pc = i,
                                Instruction::If { end_pc, else_pc: ep, .. } => {
                                    *end_pc = i;
                                    *ep = else_pc;
                                }
                                _ => {}
                            }
                        }
                        _ => {} // Loop doesn't need end_pc
                    }
                }
            }
            _ => {}
        }
    }
}

pub(crate) fn decode_block_type(bt: wasmparser::BlockType) -> BlockType {
    match bt {
        wasmparser::BlockType::Empty => BlockType::Empty,
        wasmparser::BlockType::Type(ty) => BlockType::Val(ty),
        wasmparser::BlockType::FuncType(idx) => BlockType::FuncType(idx),
    }
}

pub(crate) fn decode_op(op: &Operator) -> Option<Instruction> {
    Some(match *op {
        Operator::Unreachable => Instruction::Unreachable,
        Operator::Nop => Instruction::Nop,
        Operator::Block { blockty } => Instruction::Block { ty: decode_block_type(blockty), end_pc: 0 },
        Operator::Loop { blockty } => Instruction::Loop { ty: decode_block_type(blockty) },
        Operator::If { blockty } => Instruction::If { ty: decode_block_type(blockty), end_pc: 0, else_pc: None },
        Operator::Else => Instruction::Else,
        Operator::End => Instruction::End,
        Operator::Br { relative_depth } => Instruction::Br(relative_depth),
        Operator::BrIf { relative_depth } => Instruction::BrIf(relative_depth),
        Operator::BrTable { ref targets } => Instruction::BrTable {
            targets: targets.targets().collect::<Result<Vec<_>, _>>().ok()?,
            default: targets.default(),
        },
        Operator::Return => Instruction::Return,
        Operator::Call { function_index } => Instruction::Call(function_index),
        Operator::CallIndirect { type_index, table_index } => Instruction::CallIndirect {
            type_idx: type_index,
            table_idx: table_index,
        },
        Operator::Drop => Instruction::Drop,
        Operator::Select => Instruction::Select,
        Operator::TypedSelect { .. } => Instruction::Select,

        Operator::LocalGet { local_index } => Instruction::LocalGet(local_index),
        Operator::LocalSet { local_index } => Instruction::LocalSet(local_index),
        Operator::LocalTee { local_index } => Instruction::LocalTee(local_index),
        Operator::GlobalGet { global_index } => Instruction::GlobalGet(global_index),
        Operator::GlobalSet { global_index } => Instruction::GlobalSet(global_index),

        Operator::I32Load { memarg } => Instruction::I32Load(memarg.offset),
        Operator::I64Load { memarg } => Instruction::I64Load(memarg.offset),
        Operator::F32Load { memarg } => Instruction::F32Load(memarg.offset),
        Operator::F64Load { memarg } => Instruction::F64Load(memarg.offset),
        Operator::I32Load8S { memarg } => Instruction::I32Load8S(memarg.offset),
        Operator::I32Load8U { memarg } => Instruction::I32Load8U(memarg.offset),
        Operator::I32Load16S { memarg } => Instruction::I32Load16S(memarg.offset),
        Operator::I32Load16U { memarg } => Instruction::I32Load16U(memarg.offset),
        Operator::I64Load8S { memarg } => Instruction::I64Load8S(memarg.offset),
        Operator::I64Load8U { memarg } => Instruction::I64Load8U(memarg.offset),
        Operator::I64Load16S { memarg } => Instruction::I64Load16S(memarg.offset),
        Operator::I64Load16U { memarg } => Instruction::I64Load16U(memarg.offset),
        Operator::I64Load32S { memarg } => Instruction::I64Load32S(memarg.offset),
        Operator::I64Load32U { memarg } => Instruction::I64Load32U(memarg.offset),
        Operator::I32Store { memarg } => Instruction::I32Store(memarg.offset),
        Operator::I64Store { memarg } => Instruction::I64Store(memarg.offset),
        Operator::F32Store { memarg } => Instruction::F32Store(memarg.offset),
        Operator::F64Store { memarg } => Instruction::F64Store(memarg.offset),
        Operator::I32Store8 { memarg } => Instruction::I32Store8(memarg.offset),
        Operator::I32Store16 { memarg } => Instruction::I32Store16(memarg.offset),
        Operator::I64Store8 { memarg } => Instruction::I64Store8(memarg.offset),
        Operator::I64Store16 { memarg } => Instruction::I64Store16(memarg.offset),
        Operator::I64Store32 { memarg } => Instruction::I64Store32(memarg.offset),
        Operator::MemorySize { .. } => Instruction::MemorySize,
        Operator::MemoryGrow { .. } => Instruction::MemoryGrow,

        Operator::I32Const { value } => Instruction::I32Const(value),
        Operator::I64Const { value } => Instruction::I64Const(value),
        Operator::F32Const { value } => Instruction::F32Const(f32::from_bits(value.bits())),
        Operator::F64Const { value } => Instruction::F64Const(f64::from_bits(value.bits())),

        Operator::I32Eqz => Instruction::I32Eqz,
        Operator::I32Eq => Instruction::I32Eq,
        Operator::I32Ne => Instruction::I32Ne,
        Operator::I32LtS => Instruction::I32LtS,
        Operator::I32LtU => Instruction::I32LtU,
        Operator::I32GtS => Instruction::I32GtS,
        Operator::I32GtU => Instruction::I32GtU,
        Operator::I32LeS => Instruction::I32LeS,
        Operator::I32LeU => Instruction::I32LeU,
        Operator::I32GeS => Instruction::I32GeS,
        Operator::I32GeU => Instruction::I32GeU,
        Operator::I32Clz => Instruction::I32Clz,
        Operator::I32Ctz => Instruction::I32Ctz,
        Operator::I32Popcnt => Instruction::I32Popcnt,
        Operator::I32Add => Instruction::I32Add,
        Operator::I32Sub => Instruction::I32Sub,
        Operator::I32Mul => Instruction::I32Mul,
        Operator::I32DivS => Instruction::I32DivS,
        Operator::I32DivU => Instruction::I32DivU,
        Operator::I32RemS => Instruction::I32RemS,
        Operator::I32RemU => Instruction::I32RemU,
        Operator::I32And => Instruction::I32And,
        Operator::I32Or => Instruction::I32Or,
        Operator::I32Xor => Instruction::I32Xor,
        Operator::I32Shl => Instruction::I32Shl,
        Operator::I32ShrS => Instruction::I32ShrS,
        Operator::I32ShrU => Instruction::I32ShrU,
        Operator::I32Rotl => Instruction::I32Rotl,
        Operator::I32Rotr => Instruction::I32Rotr,

        Operator::I64Eqz => Instruction::I64Eqz,
        Operator::I64Eq => Instruction::I64Eq,
        Operator::I64Ne => Instruction::I64Ne,
        Operator::I64LtS => Instruction::I64LtS,
        Operator::I64LtU => Instruction::I64LtU,
        Operator::I64GtS => Instruction::I64GtS,
        Operator::I64GtU => Instruction::I64GtU,
        Operator::I64LeS => Instruction::I64LeS,
        Operator::I64LeU => Instruction::I64LeU,
        Operator::I64GeS => Instruction::I64GeS,
        Operator::I64GeU => Instruction::I64GeU,
        Operator::I64Clz => Instruction::I64Clz,
        Operator::I64Ctz => Instruction::I64Ctz,
        Operator::I64Popcnt => Instruction::I64Popcnt,
        Operator::I64Add => Instruction::I64Add,
        Operator::I64Sub => Instruction::I64Sub,
        Operator::I64Mul => Instruction::I64Mul,
        Operator::I64DivS => Instruction::I64DivS,
        Operator::I64DivU => Instruction::I64DivU,
        Operator::I64RemS => Instruction::I64RemS,
        Operator::I64RemU => Instruction::I64RemU,
        Operator::I64And => Instruction::I64And,
        Operator::I64Or => Instruction::I64Or,
        Operator::I64Xor => Instruction::I64Xor,
        Operator::I64Shl => Instruction::I64Shl,
        Operator::I64ShrS => Instruction::I64ShrS,
        Operator::I64ShrU => Instruction::I64ShrU,
        Operator::I64Rotl => Instruction::I64Rotl,
        Operator::I64Rotr => Instruction::I64Rotr,

        Operator::I32WrapI64 => Instruction::I32WrapI64,
        Operator::I64ExtendI32S => Instruction::I64ExtendI32S,
        Operator::I64ExtendI32U => Instruction::I64ExtendI32U,

        Operator::F32Eq => Instruction::F32Eq,
        Operator::F32Ne => Instruction::F32Ne,
        Operator::F32Lt => Instruction::F32Lt,
        Operator::F32Gt => Instruction::F32Gt,
        Operator::F32Le => Instruction::F32Le,
        Operator::F32Ge => Instruction::F32Ge,
        Operator::F64Eq => Instruction::F64Eq,
        Operator::F64Ne => Instruction::F64Ne,
        Operator::F64Lt => Instruction::F64Lt,
        Operator::F64Gt => Instruction::F64Gt,
        Operator::F64Le => Instruction::F64Le,
        Operator::F64Ge => Instruction::F64Ge,
        Operator::F32Abs => Instruction::F32Abs,
        Operator::F32Neg => Instruction::F32Neg,
        Operator::F32Ceil => Instruction::F32Ceil,
        Operator::F32Floor => Instruction::F32Floor,
        Operator::F32Trunc => Instruction::F32Trunc,
        Operator::F32Nearest => Instruction::F32Nearest,
        Operator::F32Sqrt => Instruction::F32Sqrt,
        Operator::F32Add => Instruction::F32Add,
        Operator::F32Sub => Instruction::F32Sub,
        Operator::F32Mul => Instruction::F32Mul,
        Operator::F32Div => Instruction::F32Div,
        Operator::F32Min => Instruction::F32Min,
        Operator::F32Max => Instruction::F32Max,
        Operator::F32Copysign => Instruction::F32Copysign,
        Operator::F64Abs => Instruction::F64Abs,
        Operator::F64Neg => Instruction::F64Neg,
        Operator::F64Ceil => Instruction::F64Ceil,
        Operator::F64Floor => Instruction::F64Floor,
        Operator::F64Trunc => Instruction::F64Trunc,
        Operator::F64Nearest => Instruction::F64Nearest,
        Operator::F64Sqrt => Instruction::F64Sqrt,
        Operator::F64Add => Instruction::F64Add,
        Operator::F64Sub => Instruction::F64Sub,
        Operator::F64Mul => Instruction::F64Mul,
        Operator::F64Div => Instruction::F64Div,
        Operator::F64Min => Instruction::F64Min,
        Operator::F64Max => Instruction::F64Max,
        Operator::F64Copysign => Instruction::F64Copysign,

        Operator::I32TruncF32S => Instruction::I32TruncF32S,
        Operator::I32TruncF32U => Instruction::I32TruncF32U,
        Operator::I32TruncF64S => Instruction::I32TruncF64S,
        Operator::I32TruncF64U => Instruction::I32TruncF64U,
        Operator::I64TruncF32S => Instruction::I64TruncF32S,
        Operator::I64TruncF32U => Instruction::I64TruncF32U,
        Operator::I64TruncF64S => Instruction::I64TruncF64S,
        Operator::I64TruncF64U => Instruction::I64TruncF64U,
        Operator::F32ConvertI32S => Instruction::F32ConvertI32S,
        Operator::F32ConvertI32U => Instruction::F32ConvertI32U,
        Operator::F32ConvertI64S => Instruction::F32ConvertI64S,
        Operator::F32ConvertI64U => Instruction::F32ConvertI64U,
        Operator::F32DemoteF64 => Instruction::F32DemoteF64,
        Operator::F64ConvertI32S => Instruction::F64ConvertI32S,
        Operator::F64ConvertI32U => Instruction::F64ConvertI32U,
        Operator::F64ConvertI64S => Instruction::F64ConvertI64S,
        Operator::F64ConvertI64U => Instruction::F64ConvertI64U,
        Operator::F64PromoteF32 => Instruction::F64PromoteF32,
        Operator::I32ReinterpretF32 => Instruction::I32ReinterpretF32,
        Operator::I64ReinterpretF64 => Instruction::I64ReinterpretF64,
        Operator::F32ReinterpretI32 => Instruction::F32ReinterpretI32,
        Operator::F64ReinterpretI64 => Instruction::F64ReinterpretI64,

        Operator::I32Extend8S => Instruction::I32Extend8S,
        Operator::I32Extend16S => Instruction::I32Extend16S,
        Operator::I64Extend8S => Instruction::I64Extend8S,
        Operator::I64Extend16S => Instruction::I64Extend16S,
        Operator::I64Extend32S => Instruction::I64Extend32S,

        Operator::I32TruncSatF32S => Instruction::I32TruncSatF32S,
        Operator::I32TruncSatF32U => Instruction::I32TruncSatF32U,
        Operator::I32TruncSatF64S => Instruction::I32TruncSatF64S,
        Operator::I32TruncSatF64U => Instruction::I32TruncSatF64U,
        Operator::I64TruncSatF32S => Instruction::I64TruncSatF32S,
        Operator::I64TruncSatF32U => Instruction::I64TruncSatF32U,
        Operator::I64TruncSatF64S => Instruction::I64TruncSatF64S,
        Operator::I64TruncSatF64U => Instruction::I64TruncSatF64U,

        Operator::RefFunc { function_index } => Instruction::RefFunc(function_index),
        Operator::RefNull { .. } => Instruction::RefNull,

        Operator::RefIsNull => Instruction::RefIsNull,

        Operator::TableInit { elem_index, table } => Instruction::TableInit { elem_idx: elem_index, table_idx: table },
        Operator::ElemDrop { elem_index } => Instruction::ElemDrop(elem_index),
        Operator::MemoryInit { data_index, mem: 0 } => Instruction::MemoryInit(data_index),
        Operator::DataDrop { data_index } => Instruction::DataDrop(data_index),
        Operator::MemoryCopy { dst_mem: 0, src_mem: 0 } => Instruction::MemoryCopy,
        Operator::MemoryFill { mem: 0 } => Instruction::MemoryFill,

        Operator::TableGet { table } => Instruction::TableGet(table),
        Operator::TableSet { table } => Instruction::TableSet(table),
        Operator::TableGrow { table } => Instruction::TableGrow(table),
        Operator::TableSize { table } => Instruction::TableSize(table),
        Operator::TableCopy { dst_table, src_table } => Instruction::TableCopy { dst_table, src_table },
        Operator::TableFill { table } => Instruction::TableFill(table),

        _ => return None,
    })
}

/// Peephole optimization pass: fuse common instruction sequences into superinstructions.
/// Replaces consumed instructions with Nop to preserve body length and all PC offsets.
pub(crate) fn peephole_optimize(body: &mut [Instruction]) {
    let len = body.len();
    let mut i = 0;
    while i + 1 < len {
        match (&body[i], &body[i + 1]) {
            // LocalGet + I32Const -> LocalGetI32Const
            (Instruction::LocalGet(idx), Instruction::I32Const(val)) => {
                let idx = *idx;
                let val = *val;
                body[i] = Instruction::LocalGetI32Const(idx, val);
                body[i + 1] = Instruction::Nop;
                i += 2;
            }
            // LocalGet + LocalGet -> LocalGetLocalGet
            (Instruction::LocalGet(a), Instruction::LocalGet(b)) => {
                let a = *a;
                let b = *b;
                body[i] = Instruction::LocalGetLocalGet(a, b);
                body[i + 1] = Instruction::Nop;
                i += 2;
            }
            _ => {
                i += 1;
            }
        }
    }
}
