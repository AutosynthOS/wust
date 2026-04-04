//! Wasm-to-graph builder.

pub mod block;
pub mod compile;
pub mod function;
pub mod graph;
pub mod region;
pub mod state;

pub use autosynth_isa::Width;

/// Block identifier — matches wasm PCs for user blocks.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BlockId {
    Entry(u32),
    User(u32),
    Gen(u32),
}
