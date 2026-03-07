use crate::debugger::Debugger;
use crate::ir::function::IRFunction;

/// Collects finalized [`IRFunction`]s from one or more [`FunctionBuilder`](super::FunctionBuilder)s.
///
/// Acts as the compilation unit — the caller builds functions individually,
/// then hands the `CodeBuilder` to a backend for lowering.
///
/// Optionally holds a [`Debugger`] for collecting debug traces. Access the
/// debugger via [`dbg`](Self::dbg) — the closure is never called when no
/// debugger is attached, so formatting and allocations are avoided entirely.
pub struct CodeBuilder {
    functions: Vec<IRFunction>,
    debugger: Option<Debugger>,
}

impl CodeBuilder {
    /// Create an empty code builder with no debugger.
    pub fn new() -> Self {
        Self {
            functions: Vec::new(),
            debugger: None,
        }
    }

    /// Attach a debugger for collecting debug traces.
    pub fn attach_debugger(&mut self, debugger: Debugger) {
        self.debugger = Some(debugger);
    }

    /// Take the debugger out (e.g. after compilation, for rendering).
    pub fn take_debugger(&mut self) -> Option<Debugger> {
        self.debugger.take()
    }

    /// Run a closure with the debugger if one is attached.
    ///
    /// When no debugger is present the closure is never called — no string
    /// formatting, no allocations, zero cost.
    pub fn dbg(&mut self, f: impl FnOnce(&mut Debugger)) {
        if let Some(dbg) = &mut self.debugger {
            f(dbg);
        }
    }

    /// Accept a finalized function IR produced by [`FunctionBuilder::build`](super::FunctionBuilder::build).
    ///
    /// If a debugger is attached, automatically populates block metadata
    /// (params/results) from the finalized IR blocks.
    pub fn push_function(&mut self, func: IRFunction) {
        if let Some(dbg) = &mut self.debugger {
            for block in &func.blocks {
                let params: Vec<String> = block
                    .params
                    .iter()
                    .map(|vreg| {
                        let def = &func.vreg_defs[vreg.0 as usize];
                        format!("{}<{}>", vreg, def.ty)
                    })
                    .collect();
                let results: Vec<String> = block
                    .results
                    .iter()
                    .map(|vreg| {
                        let def = &func.vreg_defs[vreg.0 as usize];
                        format!("{}<{}>", vreg, def.ty)
                    })
                    .collect();
                dbg.set_block_meta(block.id, params, results);
            }
        }
        self.functions.push(func);
    }

    /// Access the collected function IRs as a slice.
    pub fn functions(&self) -> &[IRFunction] {
        &self.functions
    }
}
