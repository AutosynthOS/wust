/// Dream jit_module.rs — the API we WANT.
///
/// This sketches the ideal compile_func using the new VCode pipeline.
/// Types/methods that don't exist yet are used freely — we'll build
/// backwards from this to create the traits and types we need.
use autosynth_ir::{AluOp, BlockId, CompOp, VCode};
use autosynth_isa::Width;
use wust_core::{FRAME_HEADER_SIZE, FuncMeta, OpCode, slot_size};

use crate::conversion::valtype_to_width;

/// Compile a single WASM function into VCode.
///
/// `f` is the wust-specific function builder that wraps the autosynth
/// builder. It manages wasm regions (locals, operands, fibre) and
/// emits VCode + operands to the underlying builder.
fn compile_func(f: &mut WasmFunctionBuilder, func: &FuncMeta, all_funcs: &[FuncMeta]) {
    // --- Prologue ---

    // Declare parameters — each arrives in a CC register.
    for (i, param) in func.params.iter().enumerate() {
        let w = valtype_to_width(param);
        f.declare_param(i, w);
    }

    // Declare zero-initialized locals.
    for local in func.locals.iter() {
        let w = valtype_to_width(local);
        f.declare_local(w);
    }

    // Save link register onto the fibre stack.
    f.save_lr();

    // Branch to first user block.
    f.br(BlockId::User(0));
    f.start_block(BlockId::User(0));

    // --- Main compilation loop ---
    let mut pc = 0;
    loop {
        let inline_op = &func.body.ops[pc];
        let op = inline_op.opcode();

        match op {
            // --- Constants and locals ---
            OpCode::I32Const => {
                let value = inline_op.immediate_i32();
                f.push_const(value as i64);
            }
            OpCode::LocalGetI32 => {
                let idx = inline_op.local_index() as usize;
                f.push_local(idx);
            }
            OpCode::LocalSetI32 => {
                let idx = inline_op.local_index() as usize;
                let val = f.pop();
                f.local_set(idx, val);
            }

            // --- Arithmetic ---
            OpCode::I32Add => f.binop(AluOp::Add),
            OpCode::I32Sub => f.binop(AluOp::Sub),
            OpCode::I32LeS => f.binop(AluOp::Comp(CompOp::LeS)),
            OpCode::I32Eqz => {
                let val = f.pop();
                let zero = f.const_vreg(0);
                f.push_cmp(CompOp::Eq, val, zero);
            }

            // --- Control flow ---
            OpCode::If => {
                let block_idx = inline_op.immediate_u32();
                let block = &func.body.blocks[block_idx as usize];
                let cond = f.pop();
                let then_block = BlockId::User(pc as u32 + 1);
                let false_target = if block.else_pc != 0 {
                    BlockId::User(block.else_pc + 1)
                } else {
                    BlockId::User(block.end_pc)
                };
                f.br_if(cond, then_block, false_target);
                f.start_block(then_block);
            }
            OpCode::Else => {
                let block_idx = inline_op.immediate_u32();
                let end_pc = func.body.blocks[block_idx as usize].end_pc;
                if !f.is_block_finalized() {
                    f.br(BlockId::User(end_pc));
                }
                f.start_block(BlockId::User(pc as u32 + 1));
            }
            OpCode::BrIf => {
                let block_idx = inline_op.immediate_u32();
                let target_block = &func.body.blocks[block_idx as usize];
                let target = BlockId::User(target_block.end_pc);
                let cont = BlockId::User(pc as u32 + 1);
                let cond = f.pop();
                f.br_if(cond, target, cont);
                f.start_block(cont);
            }
            OpCode::End => {
                let block_idx = inline_op.immediate_u32();
                if block_idx == 0 {
                    // Function end — emit epilogue and return.
                    f.emit_return(func);
                    break;
                }
                if !f.is_block_finalized() {
                    f.br(BlockId::User(pc as u32));
                }
                f.start_block(BlockId::User(pc as u32));
            }
            OpCode::Return => {
                f.emit_return(func);
            }

            // --- Calls ---
            OpCode::Call => {
                let callee_idx = inline_op.immediate_i32();
                let callee = &all_funcs[callee_idx as usize];

                // Pop args from the wasm operand stack.
                let args: Vec<VReg> = (0..callee.params.len()).rev().map(|i| f.pop()).collect();

                // call() handles everything:
                // 1. Save dirty locals/fibre to memory
                // 2. Set args into CC registers
                // 3. Frame advance
                // 4. Emit bl
                // 5. Frame restore
                // 6. Fuel check (if enabled)
                let result = f.call(callee_idx as u32, &args, callee, pc);

                // Push result onto wasm operand stack.
                if !callee.results.is_empty() {
                    f.push(result);
                }
            }

            _ => todo!("unhandled opcode: {:?}", op),
        }

        pc += 1;
    }
}

// --- Placeholder types (to be implemented) ---

struct WasmFunctionBuilder {
    // Wasm-level state:
    // - locals region (VRegion tracking local VRegs + their slots)
    // - operands region (wasm operand stack)
    // - fibre region (lr save slot)
    //
    // Wraps an autosynth-codegen builder that receives VCode + operands.
}

// VReg will come from autosynth-ir once we define the new VReg type
// for the VCode pipeline. For now, placeholder.
#[derive(Clone, Copy)]
struct VReg;

impl WasmFunctionBuilder {
    /// Push a constant onto the wasm operand stack.
    /// Allocates a VReg with Const origin.
    fn push_const(&mut self, val: i64) {
        todo!()
    }

    /// Push a local's VReg onto the wasm operand stack.
    /// The local retains its reference — this is a read, not a move.
    fn push_local(&mut self, idx: usize) {
        todo!()
    }

    /// Pop the top value from the wasm operand stack.
    fn pop(&mut self) -> VReg {
        todo!()
    }

    /// Push a VReg onto the wasm operand stack.
    fn push(&mut self, vreg: VReg) {
        todo!()
    }

    /// Write a value into a local slot.
    fn local_set(&mut self, idx: usize, val: VReg) {
        todo!()
    }

    /// Emit an ALU binary op: pop two, push result.
    /// Emits VCode::Alu + pushes operands to the vcode operand stack.
    fn binop(&mut self, op: AluOp) {
        let rhs = self.pop();
        let lhs = self.pop();
        let dst = todo!("allocate result vreg");
        // Push operands to vcode stack, emit instruction
        // self.builder.push_operand(lhs);
        // self.builder.push_operand(rhs);
        // self.builder.push_operand(dst);
        // self.builder.emit(VCode::Alu { op });
        self.push(dst);
    }

    /// Compare two values, push the condition result.
    fn push_cmp(&mut self, op: CompOp, lhs: VReg, rhs: VReg) {
        todo!()
    }

    /// Allocate a VReg for a constant value.
    fn const_vreg(&mut self, val: i64) -> VReg {
        todo!()
    }

    /// Declare a function parameter.
    fn declare_param(&mut self, idx: usize, width: Width) {
        todo!()
    }

    /// Declare a zero-initialized local.
    fn declare_local(&mut self, width: Width) {
        todo!()
    }

    /// Save the link register to the fibre stack.
    fn save_lr(&mut self) {
        todo!()
    }

    /// Unconditional branch.
    fn br(&mut self, target: BlockId) {
        todo!()
    }

    /// Conditional branch.
    fn br_if(&mut self, cond: VReg, then_block: BlockId, else_block: BlockId) {
        todo!()
    }

    /// Start a new block.
    fn start_block(&mut self, block: BlockId) {
        todo!()
    }

    /// Is the current block finalized (already has a terminator)?
    fn is_block_finalized(&self) -> bool {
        todo!()
    }

    /// Emit a function call.
    ///
    /// Handles the full call sequence:
    /// 1. Save dirty locals/operands/fibre to canonical stack slots
    /// 2. Place args in CC registers (x0, x1, ...)
    /// 3. Advance g.lb (frame pointer) past caller's frame
    /// 4. Emit bl instruction
    /// 5. Restore g.lb
    /// 6. Emit fuel check (if enabled)
    ///
    /// Returns the result VReg (from x0 after call returns).
    fn call(&mut self, callee_idx: u32, args: &[VReg], callee: &FuncMeta, pc: usize) -> VReg {
        todo!()
    }

    /// Emit function return.
    ///
    /// Pops the result value, places it in x0, restores lr and sp, ret.
    fn emit_return(&mut self, func: &FuncMeta) {
        todo!()
    }
}
