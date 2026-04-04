//! Grid-based register allocator prototype.
//!
//! Operations and VRegs live in SlotMap arenas. The "grid" is a
//! BTreeMap<SlotKey, VRegKey> tracking which vreg occupies which
//! physical location at each point in the program. The pathfinder
//! resolves register assignments by finding paths through this grid.

pub mod builder;
pub mod display;
pub mod grid;
pub mod op;
pub mod pathfinder;
pub mod timeline;
pub mod transforms;
pub mod types;

pub use op::{AluOp, CmpOp};
pub use types::{
    resolve_input_vreg, Input, MemSlot, OpCode, OpKey, Operation, SlotKey, VRegDef, VRegKey,
};
