//! Hash-interned value state graph IR.
//!
//! Every value in the program is a `VRegRef` — a hash handle into
//! a pool of `VRegState`s. Operations take VRegRefs in and produce
//! VRegRefs out. Structural equality via hash gives free CSE.

mod pool;
mod state;
mod op;

pub use pool::{Pool, VRegRef};
pub use state::VRegState;
pub use op::Op;
