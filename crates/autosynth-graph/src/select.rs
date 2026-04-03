//! Selector pipeline — recursive, demand-driven instruction selection.

use std::collections::BTreeMap;

use crate::node::NodeRef;
use crate::op::Operand;
use crate::pool::Pool;
use crate::state::VRegState;

/// Context passed to selectors — the original hash/id for stable
/// identity lookups, and the mutable state for transformation.
pub struct SelectionCtx {
    /// Hash of the original node (before any transforms). Stable key.
    pub original: u64,
    /// Human-readable ID of the original node.
    pub id: u32,
    /// The state being transformed. Selectors mutate this.
    pub state: VRegState,
}

pub trait Selector {
    fn pre_select(&mut self, ctx: &SelectionCtx) {
        let _ = ctx;
    }
    fn select(&mut self, pool: &mut Pool, ctx: &mut SelectionCtx);

    fn reset(&mut self) {}
}

pub struct Pipeline {
    selectors: Vec<Box<dyn Selector>>,
    cache: BTreeMap<NodeRef, NodeRef>,
}

impl Pipeline {
    pub fn new() -> Self {
        Self {
            selectors: Vec::new(),
            cache: BTreeMap::new(),
        }
    }

    pub fn add(&mut self, selector: Box<dyn Selector>) {
        self.selectors.push(selector);
    }

    pub fn run(&mut self, pool: &mut Pool, roots: &[NodeRef]) -> Vec<NodeRef> {
        roots
            .iter()
            .map(|r| self.select_root(pool, r.clone()))
            .collect()
    }

    fn run_selector(&mut self, selector: usize, pool: &mut Pool, node_ref: NodeRef) -> NodeRef {
        if let Some(cached) = self.cache.get(&node_ref) {
            return cached.clone();
        }

        let mut ctx = SelectionCtx {
            original: node_ref.hash_val(),
            id: node_ref.id(),
            state: node_ref.state().clone(),
        };

        self.selectors[selector].pre_select(&ctx);

        // Recurse: select each operand and effect in place
        if let Some(op) = &mut ctx.state.op {
            for operand in &mut op.uses {
                if let Operand::VReg(r) = operand {
                    *r = self.run_selector(selector, pool, r.clone());
                }
            }
            if let Some(effect) = &mut op.effect {
                *effect = self.run_selector(selector, pool, effect.clone());
            }
        }

        self.selectors[selector].select(pool, &mut ctx);

        let result = pool.intern(ctx.state);
        self.cache.insert(node_ref, result.clone());
        result
    }

    fn select_root(&mut self, pool: &mut Pool, mut node_ref: NodeRef) -> NodeRef {
        if let Some(cached) = self.cache.get(&node_ref) {
            return cached.clone();
        }

        for i in 0..self.selectors.len() {
            self.selectors[i].reset();
            node_ref = self.run_selector(i, pool, node_ref.clone());
        }

        node_ref
    }

    // fn select_node(&mut self, pool: &mut Pool, node_ref: NodeRef) -> NodeRef {
    //     if let Some(cached) = self.cache.get(&node_ref) {
    //         return cached.clone();
    //     }

    //     // Pre-select: all selectors see the original state
    //     let reversed = self.selectors.iter_mut().rev();
    //     for s in reversed {
    //         s.pre_select(&ctx);
    //     }

    //     // Recurse: select each operand and effect in place
    //     if let Some(op) = &mut ctx.state.op {
    //         for operand in &mut op.uses {
    //             if let Operand::VReg(r) = operand {
    //                 *r = self.select_node(pool, r.clone());
    //             }
    //         }
    //         if let Some(effect) = &mut op.effect {
    //             *effect = self.select_node(pool, effect.clone());
    //         }
    //     }

    //     // Select: all selectors mutate the state
    //     for s in &mut self.selectors {
    //         s.select(pool, &mut ctx);
    //     }

    //     let result = pool.intern(ctx.state);
    //     self.cache.insert(node_ref, result.clone());
    //     result
    // }
}
