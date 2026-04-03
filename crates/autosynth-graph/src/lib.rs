#![feature(deref_patterns, deref_pure_trait)]
#![allow(incomplete_features)]

//! Hash-interned value state graph IR.
//!
//! Every value in the program is a `NodeRef` — an Rc-backed handle into
//! a pool of `VRegState`s. Operations take NodeRefs in and produce
//! NodeRefs out. Structural equality via hash gives free CSE.
//! Dead subtrees clean up automatically via reference counting.

mod node;
mod pool;
mod state;
mod op;
pub mod select;
pub mod selectors;

pub use node::{Node, NodeRef};
pub use pool::Pool;
pub use state::{Define, VRegState, SlotRef};
pub use op::{AluOp, CmpOp, Op, Operand, VCode};
