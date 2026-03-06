use autosynth_codegen::{
    AluOp, BlockId, CmpOp, CodeBuilder, FunctionBuilder, FunctionIdx, IrInst, IrType, IsaReg,
    VStack, Value,
};
use autosynth_codegen::backend::aarch64::Aarch64Backend;
use autosynth_codegen::backend::BackendEmitter;
use wust_core::exec::ModuleExecutor;
use wust_core::{FRAME_HEADER_SIZE, FuncMeta, OpCode, Outcome, ParsedModule, Task, ValType};

use crate::CodeBuffer;

/// A JIT-compiled module.
///
/// Owns the parsed module, the IR compiler, and the executable code page.
pub struct JitModule {
    module: ParsedModule,
    compiler: CodeBuilder,
    page: CodeBuffer,
}

impl JitModule {
    pub fn new(module: ParsedModule) -> Result<Self, anyhow::Error> {
        let mut compiler = CodeBuilder::new();
        let page = CodeBuffer::new()?;

        for func in module.funcs.iter() {
            let mut backend = Aarch64Backend::new();
            Self::compile_func(&mut compiler, &mut backend, func)?;
        }

        Ok(JitModule {
            module,
            compiler,
            page,
        })
    }

    /// Access the compiled IR (for debugging/inspection).
    pub fn ir(&self) -> &CodeBuilder {
        &self.compiler
    }

    fn compile_func(cb: &mut CodeBuilder, backend: &mut Aarch64Backend, func: &FuncMeta) -> anyhow::Result<()> {
        let mut f = FunctionBuilder::new();

        let lbp = backend.use_isa_reg("lbp", IsaReg::FramePointer);
        let lr = backend.use_isa_reg("lr", IsaReg::ReturnAddress);
        let _fuel = backend.use_isa_reg("fuel", IsaReg::Define64(0));
        let _ctx = backend.use_isa_reg("ctx", IsaReg::Define64(1));
        let fsp = backend.use_isa_reg("fsp", IsaReg::StackPointer);

        // Virtual stacks anchored to physical registers
        //
        // [param0, param1, local_2, ...][frame header][operands]
        // ^ lbp
        let locals = f.define_vstack(VStack {
            base: lbp,
            offset: 0,
        });
        let operands = f.define_vstack(VStack {
            base: lbp,
            offset: func.locals_size as u32 + FRAME_HEADER_SIZE as u32,
        });
        let fibre = f.define_vstack(VStack {
            base: fsp,
            offset: 0,
        });

        // Declare parameters
        for (i, param) in func.params.iter().enumerate() {
            f.define_slot(locals, i, valtype_to_ir(param), Value::Param(i));
        }

        // Declare zero-initialized locals
        for (i, local) in func.locals.iter().enumerate() {
            f.define_slot(
                locals,
                i + func.params.len(),
                valtype_to_ir(&local),
                Value::Const(0),
            );
        }

        // Prologue
        f.entry_block(BlockId::Entry);
        f.label("prologue");
        f.push_i64(fibre, Value::Reg(lr));
        f.switch_to_block(BlockId::User(0));

        // Main compilation loop
        let mut pc = 0;
        loop {
            debug_assert!(pc < func.body.ops.len(), "pc {pc} out of bounds (len={})", func.body.ops.len());
            let inline_op = unsafe { func.body.ops.get_unchecked(pc) };
            let op = inline_op.opcode();

            match op {
                OpCode::I32Const => {
                    f.push_i32(operands, Value::ConstI32(inline_op.immediate_i32()));
                }

                OpCode::LocalGetI32 => {
                    let idx = inline_op.local_index();
                    let src = f.get_slot(locals, idx as usize);
                    f.push_vreg(operands, src);
                }
                OpCode::LocalSetI32 => {
                    let idx = inline_op.local_index();
                    let val = f.pop_i32(operands);
                    f.define_slot(locals, idx as usize, IrType::I32, Value::VReg(val));
                }

                OpCode::I32Add => {
                    let rhs = f.pop_i32(operands);
                    let lhs = f.pop_i32(operands);
                    let dst = f.push_i32_vreg(operands);
                    f.emit(IrInst::Alu {
                        op: AluOp::Add,
                        dst,
                        lhs,
                        rhs,
                    });
                }
                OpCode::I32Sub => {
                    let rhs = f.pop_i32(operands);
                    let lhs = f.pop_i32(operands);
                    let dst = f.push_i32_vreg(operands);
                    f.emit(IrInst::Alu {
                        op: AluOp::Sub,
                        dst,
                        lhs,
                        rhs,
                    });
                }

                OpCode::I32LeS => {
                    let rhs = f.pop_i32(operands);
                    let lhs = f.pop_i32(operands);
                    let dst = f.push_i32_vreg(operands);
                    f.emit(IrInst::Cmp {
                        op: CmpOp::LeS,
                        dst,
                        lhs,
                        rhs,
                    });
                }

                OpCode::If => {
                    let block_idx = inline_op.immediate_u32();
                    let cond = f.pop_i32(operands);
                    // Then-path enters the if-block body.
                    // Else/continuation starts after the end — at User(pc after end).
                    let then_block = BlockId::User(pc as u32 + 1);
                    let end_pc = func.body.blocks[block_idx as usize].end_pc;
                    let cont_block = BlockId::User(end_pc);
                    f.emit(IrInst::BrIf {
                        cond,
                        block_if: then_block,
                        block_else: cont_block,
                    });
                    f.switch_to_block(then_block);
                }
                OpCode::BrIf => {
                    let block_idx = inline_op.immediate_u32();
                    let target_block = &func.body.blocks[block_idx as usize];
                    let target = BlockId::User(target_block.end_pc);
                    let cont = BlockId::User(pc as u32 + 1);
                    let cond = f.pop_i32(operands);
                    f.emit(IrInst::BrIf {
                        cond,
                        block_if: target,
                        block_else: cont,
                    });
                    f.switch_to_block(cont);
                }
                OpCode::End => {
                    // Continuation block starts at this PC.
                    let block_idx = inline_op.immediate_u32();
                    f.switch_to_block(BlockId::User(pc as u32));
                    if block_idx == 0 {
                        break;
                    }
                }

                OpCode::Return => {
                    let val = f.pop_i32(operands);
                    f.pop_i64(fibre);
                    f.emit(IrInst::Return { values: vec![val] });
                }

                OpCode::Call => {
                    let func_idx = inline_op.immediate_i32();
                    if func_idx.is_negative() {
                        todo!("call to negative index function");
                    }
                    f.emit(IrInst::Call {
                        func_idx: FunctionIdx::User(func_idx as u32),
                    });
                }

                _ => todo!("unhandled opcode: {:?}", op),
            }

            pc += 1;
        }

        f.build(cb);
        Ok(())
    }
}

fn valtype_to_ir(ty: &ValType) -> IrType {
    match ty {
        ValType::I32 => IrType::I32,
        ValType::I64 => IrType::I64,
        ValType::F32 => IrType::F32,
        ValType::F64 => IrType::F64,
        ValType::V128 => IrType::V128,
        ValType::Ref(_) => todo!(),
    }
}

impl ModuleExecutor for JitModule {
    fn poll(&self, task: &mut Task) -> Outcome {
        // TODO: actually execute compiled code via asm trampoline
        task.context.wasm_fp.write_i32(0, 55);
        Outcome::Return
    }
}
